import logging
import dataclasses

import idautils

logger = logging.getLogger('HexFuncInlinerOpt')

import idaapi
from idaapi import *

_mmat_strs = {
    MMAT_ZERO: "MMAT_ZERO",
    MMAT_GENERATED: "MMAT_GENERATED",
    MMAT_PREOPTIMIZED: "MMAT_PREOPTIMIZED",
    MMAT_LOCOPT: "MMAT_LOCOPT",
    MMAT_CALLS: "MMAT_CALLS",
    MMAT_GLBOPT1: "MMAT_GLBOPT1",
    MMAT_GLBOPT2: "MMAT_GLBOPT2",
    MMAT_GLBOPT3: "MMAT_GLBOPT3",
    MMAT_LVARS: "MMAT_LVARS",
}


def mba_maturity_t_to_string(mmt):
    return _mmat_strs.get(mmt, "???")


def is_arm():
    # both arm / arm64
    inf = get_inf_structure()
    return inf.procname == "ARM"

def is_jump_mcode(mcode):
    return mcode >= m_jnz and mcode <= m_jle

def add_edge(block1, block2):
    logger.debug("Adding edge from %d to %d" % (block1.serial, block2.serial))
    block1.succset.append(block2.serial)
    block2.predset.append(block1.serial)
    pass

BLOCK_FLAG = MBL_FAKE | MBL_COMB
def copy_block(mba, ori_block, insert_loc=None):
    """
    :rtype:
    """
    if insert_loc is None:
        insert_loc = mba.qty
    mba.get_mblock(insert_loc - 1).type = BLT_NONE
    ori_block.type = BLT_NONE
    newblock = mba.copy_block(ori_block, insert_loc, CPBLK_FAST)  # type: Union[mblock_t, str]
    newblock.flags |= BLOCK_FLAG
    newblock.type = BLT_NONE
    newblock.mark_lists_dirty()
    return newblock # type: mblock_t

def create_block(mba, start, end, insert_loc=None):
    if insert_loc is None:
        insert_loc = mba.qty
    mba.get_mblock(insert_loc - 1).type = BLT_NONE
    newblock = mba.insert_block(insert_loc)
    newblock.start = start
    newblock.end = end
    newblock.type = BLT_NONE
    newblock.flags = BLOCK_FLAG
    newblock.mark_lists_dirty()
    return newblock

def is_mblock_in_range(mbl, ranges):
    """
    check if a mblock_t locates in an array of EA range
    :param mbl:
    :type mbl: mblock_t
    :param bbl:
    """
    s = mbl.start
    e = mbl.end

    if mbl.tail:
        if mbl.tail.ea > e or mbl.tail.ea < s:
            # tail's ea isn't in the range, so we must be merging
            # as we are merging, we use tail instruction's ea, so that the checking of endbbl won't be affected
            s = e = mbl.tail.ea

    for c in ranges:
        if s >= c[0] and e <= c[1]:
            return True
    return False

def is_ea_in_range(ea, ranges):
    for c in ranges:
        if ea >= c[0] and ea < c[1]:
            return True
    return False

def nop_minsn(minsn):
    if minsn is None:
        return
    minsn.iprops = 0
    minsn.l.erase()
    minsn.r.erase()
    minsn.d.erase()
    minsn.opcode = m_nop

def patch_last_goto(newblock, targetblock, noplast=True):
    if noplast:
        nop_minsn(newblock.tail)

    # you must ensure the minsn_t's ea is not BADADDR
    if not newblock.tail:
        newinsn = minsn_t(newblock.start)
    else:
        newinsn = minsn_t(newblock.tail)
    nop_minsn(newinsn)
    newinsn.opcode = m_goto
    newinsn.l.make_blkref(targetblock.serial)
    newblock.insert_into_block(newinsn, newblock.tail)
    newblock.type = BLT_1WAY
    #add_edge(newblock, targetblock)


@dataclasses.dataclass
class FlowEnds:
    jcnd_target: list = dataclasses.field(default_factory=list)
    goto_target: list = dataclasses.field(default_factory=list)
    fallthrough: list = dataclasses.field(default_factory=list)
    ret: list = dataclasses.field(default_factory=list)

def copy_blocks(mba, ori_blocks):
    """
    Copy a set of blocks, handling jcnd & gotos
    """

    # The key problem of this function is to solve the flow-out problem
    # Case 1: simple block
    # Case 2: block endswith must-end opcode (m_call/m_icall/m_ijmp)
    # Case 3: block endswith jcnd
    # Case 4: block endswith goto
    # Case 5: stop block - (ignored)
    # For case 123, code flows into next mblock, so we need to check if next block exists
    # For case 34, we have to check whether jump target flows out

    new_blocks = {}
    ori_block_id = [c.serial for c in ori_blocks]
    for oriblk in ori_blocks: # type: mblock_t
        newblk = copy_block(mba, oriblk) # type: mblock_t
        new_blocks[oriblk.serial] = newblk
        tail_opcode = oriblk.tail.opcode if oriblk.tail else None
        if oriblk.tail and (
                is_mcode_jcond(tail_opcode) # jcnd
                or is_jump_mcode(tail_opcode) # conditional jumps
                or must_mcode_close_block(tail_opcode, True) # call/icall
        ):
            # these block need a fall-through block
            if oriblk.serial + 1 not in ori_block_id:
                # fallthrough-block is not present, create it
                fallblk = create_block(mba, oriblk.tail.ea, oriblk.end)
                # not adding fallblk here because new_blocks is the oriblk-newblk map, and fallblk doesn't have oriblk

    flow_ends = FlowEnds()
    for oriblk_id, newblk in new_blocks.items():
        if newblk.tail and newblk.tail.opcode == m_goto: # Case 4 - goto
            # these blocks must flows into goto-target

            # parse goto-target
            assert newblk.tail.l.t == mop_b
            targetBlkID = newblk.tail.l.b

            if targetBlkID not in new_blocks:
                # goto-target flows out, marking as end
                flow_ends.goto_target.append(newblk)
            else:
                # goto-target still in range, so patch target to new one
                newTargetBlk = new_blocks[targetBlkID]
                newblk.tail.l.make_blkref(newTargetBlk.serial)
                add_edge(newblk, newTargetBlk)
            newblk.type = BLT_1WAY
        elif newblk.tail and is_mcode_jcond(newblk.tail.opcode) or is_jump_mcode(newblk.tail.opcode): # Case 3 - jcnd
            # these blocks are 2way blocks

            # ensure we have processed fall-through block
            assert oriblk_id + 1 in new_blocks

            # parse jcnd-target
            assert newblk.tail.d.t == mop_b
            targetBlkID = newblk.tail.d.b

            # Check jcnd target in range
            if targetBlkID not in new_blocks:
                # jcnd target flow out
                flow_ends.jcnd_target.append(newblk)
            else:
                # jcnd target still in range, patch it
                newTargetBlk = new_blocks[targetBlkID]
                newblk.tail.d.make_blkref(newTargetBlk.serial)
                add_edge(newblk, newTargetBlk)

            # Check fall-through in range
            if oriblk_id + 1 not in ori_block_id:
                # we created the must-have fallthrough block, so it's also an flow-out end
                flow_ends.fallthrough.append(new_blocks[oriblk_id + 1])
            newblk.type = BLT_2WAY
        elif newblk.tail and must_mcode_close_block(newblk.tail.opcode, True): # Case 2 - must-end opcode blocks
            # these blocks cannot be patched, we mark the fallthrough block as end instead
            if not oriblk_id + 1 in ori_block_id:
                if newblk.tail.is_tailcall() or newblk.tail.opcode == m_ijmp: # return-like instructions
                    flow_ends.ret.append(newblk)
                else:
                    flow_ends.fallthrough.append(mba.get_mblock(newblk.serial + 1))
            pass
        else: # Case 1 - simple blocks
            # these blocks must flows into next block
            # we handled fall-through block when we copy blocks, so just checking flow ends here
            newblk.type = BLT_1WAY
            if not oriblk_id + 1 in ori_block_id:
                flow_ends.fallthrough.append(newblk)

    return new_blocks, flow_ends


class MbaTransformer(object):
    def __init__(self, mba):
        self.mba = mba
    
    def prepare_mba(self):
        self.mba.build_graph()

        self.ori_serial = self.mba.qty - 1

        self.mba.pred_dict = {}
        self.mba.succ_dict = {}
        self.mba.fake_blk = []
        self.mba.blkinfo = {}
        for cur in range(self.mba.qty):
            curblock = self.mba.get_mblock(cur)
            self.mba.pred_dict[cur] = [c.serial for c in curblock.preds()]
            self.mba.succ_dict[cur] = [c.serial for c in curblock.succs()]
            if curblock.flags & MBL_FAKE:
                self.mba.fake_blk.append(cur)
            self.mba.blkinfo[cur] = (curblock.type, curblock.flags)

        for c in range(self.mba.qty):
            curblock = self.mba.get_mblock(c)
            curblock.type = BLT_NONE
            curblock.succset.clear()
            curblock.predset.clear()

        def get_succ(mb, parsed=True):
            succs = self.mba.succ_dict.get(mb.serial, None)
            if succs is None:
                raise Exception("get_succ used on non-ori block")
            return [self.mba.get_mblock(c) if parsed else c for c in succs]

        def get_pred(mb, parsed=True):
            preds = self.mba.pred_dict.get(mb.serial, None)
            if preds is None:
                raise Exception("get_pred used on non-ori block")
            return [self.mba.get_mblock(c) if parsed else c for c in preds]

        def is_fake(mb):
            assert isinstance(mb, mblock_t)
            return mb.serial in self.mba.fake_blk

        self.mba.get_succ = get_succ
        self.mba.get_pred = get_pred
        self.mba.is_fake = is_fake

    def cleanup_mba(self):
        """
        Fixup for the BLT_STOP block
        :return:
        """
        # there must be a BLT_STOP block, we create a real stop block here
        real_end_block = create_block(self.mba, BADADDR, BADADDR)
        real_end_block.type = BLT_STOP

        # the original stop block is then
        ori_end_block = self.mba.get_mblock(self.ori_serial)
        ori_end_block.type = BLT_NONE
        ori_end_block.start = self.mba.first_epilog_ea if self.mba.first_epilog_ea != BADADDR else self.mba.entry_ea
        ori_end_block.end = BADADDR
        patch_last_goto(ori_end_block, real_end_block)

        def redirect_block(block1, block2):
            for c in block1.preds():
                if c.serial + 1 == block1.serial:
                    continue
                if not (c.tail and must_mcode_close_block(c.tail.opcode, False)):
                    assert c.tail and must_mcode_close_block(c.tail.opcode, False)
                if c.tail.opcode == m_goto:
                    patch_last_goto(c, block2)
                elif is_mcode_jcond(c.tail.opcode):
                    assert c.tail.d.b == 0
                    c.tail.d.make_blkref(block2.serial)
                else:
                    raise Exception("Unknown situation!")

        #redirect_block(ori_end_block, real_end_block)
        #if self.extract_end_block is not None:
        #    redirect_block(self.extract_end_block, real_end_block)

    def debug_verify(self):
        """
        A Minimal mba.verify in python to avoid some basic interr
        """
        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            if blk.type != BLT_NONE:
                if blk.type == BLT_1WAY:
                    assert blk.nsucc() == 1
                elif blk.type == BLT_2WAY:
                    assert blk.nsucc() == 2
                elif blk.type == BLT_0WAY:
                    assert blk.nsucc() == 0

                if not blk.tail:
                    assert blk.type in (BLT_1WAY, BLT_0WAY, BLT_STOP, BLT_XTRN)
                elif is_mcode_call(blk.tail.opcode):
                    #assert blk.type == BLT_1WAY
                    pass
                elif is_mcode_jcond(blk.tail.opcode):
                    assert blk.type == BLT_2WAY
                elif blk.tail.opcode == m_goto:
                    assert blk.type == BLT_1WAY
                elif blk.tail.opcode in (m_ijmp, m_goto):
                    assert blk.type == BLT_0WAY
                else:
                    pass


            ins = blk.head
            ins_i = 0
            while ins is not None:
                if ins.ea == BADADDR:
                    raise Exception("50795")
                if ins.next is not None:
                    if must_mcode_close_block(ins.opcode, ins.d.empty()):
                        raise Exception("50864")
                ins = ins.next
                ins_i += 1

    def finalize_mba(self):
        # Rebuild the graph
        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            blk.succset.clear()
            blk.predset.clear()
            if i != 0 and i != self.mba.qty - 1:
                blk.type = BLT_NONE
            blk.mark_lists_dirty()

        self.mba.build_graph()

        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            if not blk.tail:
                continue
            if blk.tail.opcode == m_goto and blk.type == BLT_0WAY:
                blk.remove_from_block(blk.tail)

        self.mba.mark_chains_dirty()
        # self.mba.optimize_local(0)

        self.debug_verify()
        self.mba.verify(True)

    def process(self):
        pfn = self.mba.get_curfunc()  # type: func_t
        if pfn.tailqty == 0:
            return False

        # Func have tail chunks
        tailRanges = [(pfnTail.start_ea, pfnTail.end_ea) for pfnTail in pfn.tails]
        logger.info(f"Function has {len(tailRanges)} tails: {tailRanges}")

        #############################################################################
        # Phase I - Prepare
        #  Prepare the mba for process & find out the needed function mblock
        #############################################################################
        logger.info("Preparing basic infos...")
        self.prepare_mba()

        neededTail = {}
        for i in range(self.mba.qty):
            curblk = self.mba.get_mblock(i)
            curtail = curblk.tail  # type: minsn_t
            if curtail and curtail.opcode == m_call:
                if curtail.l.t == mop_v:
                    callAddr = curtail.l.g
                    inranges = [r for r in tailRanges if callAddr >= r[0] and callAddr < r[1]]
                    assert len(inranges) <= 1
                    if inranges:
                        neededTail[i] = inranges[0]

        logger.info("We need these tails: ", neededTail)
        tailBlocks = {}
        for r in set(neededTail.values()):
            tailBlocks[r] = []
            for cur in range(self.mba.qty):
                curblock = self.mba.get_mblock(cur)  # type: mblock_t
                if is_mblock_in_range(curblock, [r]):
                    tailBlocks[r].append(curblock)
            tailBlocks[r].sort(key=lambda blk: abs(blk.start - r[0]))

        # All function tail should have corresponding MB
        assert all(c for c in tailBlocks.values())

        #############################################################################
        # Phase II - Process each inline call
        #
        #############################################################################
        logger.info("Processing inline calls...")
        for callblkId, callRange in neededTail.items():
            callblk = self.mba.get_mblock(callblkId)  # type: mblock_t
            returnblk = self.mba.get_mblock(callblkId + 1)  # type: mblock_t
            tailBlock = tailBlocks[callRange]
            logger.info("   Processing call: %d %s", callblkId, callRange)
            newTailBlock, newEnds = copy_blocks(self.mba, tailBlock)

            newTailBlockStart = newTailBlock[tailBlock[0].serial]

            logger.info("Patching call blk %d goto %d", callblk.serial, tailBlock[0].serial)
            patch_last_goto(callblk, newTailBlockStart, True)

            # patch newblock's end to
            assert newEnds.goto_target == []
            assert newEnds.jcnd_target == []
            assert newEnds.fallthrough == []
            for end in newEnds.ret:
                logger.info("Patching end blk %d goto %d", end.serial, returnblk.serial)
                patch_last_goto(end, returnblk, True)


        # Cleanup
        self.cleanup_mba()

        # Finalize
        self.finalize_mba()


class HexFuncInlinerOpt(Hexrays_Hooks):

    def __init__(self):
        Hexrays_Hooks.__init__(self)

    def preoptimized(self, mba):
        return self._handle(mba)

    def microcode(self, mba):
        return self._handle(mba)

    def maturity(self, cfunc, new_maturity):
        return 0

    def prealloc(self, mba):
        return 0

    def locopt(self, mba: mbl_array_t):
        return 0

    def _handle(self, mba):
        """
        Start handling
        :param mbl_array_t mba: mba to handle
        :return:
        """
        logging.getLogger().setLevel(logging.DEBUG)
        logger.info("Block optimization called at maturity level %s" %
                    mba_maturity_t_to_string(mba.maturity))
        logger.info("Requested maturity level %s" % mba.reqmat)

        # We only operate at MMAT_PREOPTIMIZED
        cur_mat = mba.maturity + 1
        if not is_arm():
            process_mat = MMAT_PREOPTIMIZED
        else:
            process_mat = MMAT_GENERATED

        if cur_mat != process_mat or not mba.use_frame():  # for debug
            logger.info("Ignoring...")
            return 0

        try:
            logger.info("Got to deobfuscate now...")
            funaddr = mba.entry_ea
            self.doTransform(mba)
        except:
            import traceback
            traceback.print_exc()
            return MERR_BUSY

        return 0

    def doTransform(self, mba: mba_t):
        trans = MbaTransformer(mba)
        trans.process()

class ConvertToTailHandler(idaapi.action_handler_t):
    def __init__(self):
        idaapi.action_handler_t.__init__(self)

    # Say hello when invoked.
    def activate(self, ctx):
        cur_ea = idaapi.get_screen_ea()
        pfnChunk = idaapi.get_fchunk(cur_ea) # type: func_t
        if pfnChunk.flags & idaapi.FUNC_TAIL:
            # Already a tail, refuse to continue
            idaapi.warning("Current pos is already a function tail!")
            return 0

        curRange = (pfnChunk.start_ea, pfnChunk.end_ea)
        print("Converting chunk %x-%x to tail!" % curRange)
        funcs = set()
        for xref in idautils.XrefsTo(curRange[0], 0):
            if not xref.iscode:
                continue

            funcs.add(idaapi.get_func(xref.frm).start_ea)

        idaapi.del_func(cur_ea)
        for fun in funcs:
            print("idaapi.append_func_tail(idaapi.get_func(0x%x), 0x%x, 0x%x)" % (fun, curRange[0], curRange[1]))
            if not idaapi.append_func_tail(idaapi.get_func(fun), *curRange):
                print("    Failed to append tail to function %x" % fun)
        return 1

    # This action is always available.
    def update(self, ctx):
        return idaapi.AST_ENABLE_ALWAYS


action_desc1_name = 'hexfuncinliner:convert_to_tail'
action_desc1_menu = 'Edit/HexFuncInliner/'

action_desc1 = idaapi.action_desc_t(
            'hexfuncinliner:convert_to_tail',  # The action name. This acts like an ID and must be unique
            'Convert function to func tail',  # The action text.
            ConvertToTailHandler(),  # The action handler.
            'Ctrl-Alt-T',  # Optional: the action shortcut
            'Convert function to func tail',  # Optional: the action tooltip (available in menus/toolbar)
        )

import sys

def load():
    sys.modules['__main__'].inlineopt = HexFuncInlinerOpt()
    sys.modules['__main__'].inlineopt.hook()

    if idaapi.register_action(action_desc1):
        idaapi.attach_action_to_menu(
            action_desc1_menu,
            action_desc1_name,
            idaapi.SETMENU_APP)

def unload():
    try:
        sys.modules['__main__'].inlineopt.unhook()
    except:
        pass
    idaapi.detach_action_from_menu(action_desc1_menu, action_desc1_name)
    idaapi.unregister_action(action_desc1_name)


print("Reloaded HexFuncInliner!!")

unload()
load()