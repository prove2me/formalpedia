-- Prove2me | solution 1 for BitDFT.first_coordinate_postprocess_composed_run_v3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:43:01.021531+00:00
-- url     : https://prove2.me/submissions/fb48d91f-f77e-402d-a476-199542b8b5f7

import Definitions.Def_BitDFT_BeginAtStateV2
import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_signed_block_final_slots
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_BitDFT_extraction_ready
import Theorems.Thm_BitDFT_signed_block_initial_match
import Theorems.Thm_BitDFT_signed_block_placement_correct
import Theorems.Thm_BitDFT_first_coordinate_actual_terminator_rewind_copy_frame
import Theorems.Thm_BitDFT_first_coordinate_execution
import Theorems.Thm_BitDFT_first_coordinate_record_layout_for_copy
open BitDFT.RecordSuffixCopy BitDFT.SuffixCopyTwoTape IntMul

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl
def native_cfg {M : MultitapeTM} (c : M.Cfg) :
    (BitDFT.MachineSequence.native M).machine.Cfg := ⟨c.state,c.cells,c.head⟩

theorem native_init_cfg {M : MultitapeTM} (input extra : List Bool) :
    native_cfg (M.initCfg input extra) =
      (BitDFT.MachineSequence.native M).machine.initCfg input extra := by
  rfl

theorem native_step_cfg {M : MultitapeTM} (c : M.Cfg) :
    (BitDFT.MachineSequence.native M).machine.step (native_cfg c) = native_cfg (M.step c) := by
  rfl

theorem native_run_cfg {M : MultitapeTM} (c : M.Cfg) (t : ℕ) :
    (BitDFT.MachineSequence.native M).machine.step^[t] (native_cfg c) =
      native_cfg (M.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    calc
      _ = (BitDFT.MachineSequence.native M).machine.step
          ((BitDFT.MachineSequence.native M).machine.step^[t] (native_cfg c)) :=
            Function.iterate_succ_apply' _ _ _
      _ = native_cfg (M.step (M.step^[t] c)) := by rw [ih,native_step_cfg]
      _ = native_cfg (M.step^[t+1] c) := by rw [Function.iterate_succ_apply']


theorem begin_at_state_step {M : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller M) (q : P.K)
    (c : (BitDFT.MachineSequence.sequence P Q).machine.Cfg) :
    (begin_at_state P Q q).machine.step (to_begin_at_state_cfg P Q q c) =
      to_begin_at_state_cfg P Q q ((BitDFT.MachineSequence.sequence P Q).machine.step c) := by rfl
theorem begin_at_state_run {M : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller M) (q : P.K)
    (c : (BitDFT.MachineSequence.sequence P Q).machine.Cfg) (u : ℕ) :
    (begin_at_state P Q q).machine.step^[u] (to_begin_at_state_cfg P Q q c) =
      to_begin_at_state_cfg P Q q
        ((BitDFT.MachineSequence.sequence P Q).machine.step^[u] c) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [Function.iterate_succ_apply', ih, begin_at_state_step,
      Function.iterate_succ_apply']
theorem solution (M : MultitapeTM)
    (c : (BitDFT.VectorReady.machine M).Cfg)
    (input extra : List Bool) (T : ℕ)
    (hrun : (BitDFT.VectorReady.machine M).step^[T]
      ((BitDFT.VectorReady.machine M).initCfg input extra) = c)
    (hhalt : c.state = (BitDFT.VectorReady.machine M).qHalt)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (sign : Bool) (x y : List Bool)
    (hroot : c.cells ⟨0,by change 0 < 4+(M.k+3); omega⟩ =
      fun p => BitDFT.PreprocessorAlphabet.encode (BitDFT.VectorReady.machine M) (rootCells p))
    (hrootHead : c.head ⟨0,by change 0 < 4+(M.k+3); omega⟩ = rootHead)
    (hv : c.cells ⟨1,by change 1 < 4+(M.k+3); omega⟩ =
      (BitDFT.VectorReady.machine M).tapeOf ((sign::x).map (BitDFT.VectorReady.machine M).bitSym))
    (hvHead : c.head ⟨1,by change 1 < 4+(M.k+3); omega⟩ = 1)
    (hc : c.cells (BitDFT.DescriptorPlacement.counterTape M.k) =
      (BitDFT.VectorReady.machine M).tapeOf
        ((BitDFT.VectorReady.machine M).sep :: (y.map (BitDFT.VectorReady.machine M).bitSym ++
          [(BitDFT.VectorReady.machine M).sep])))
    (hcHead : c.head (BitDFT.DescriptorPlacement.counterTape M.k) = y.length+1)
    (ht : c.cells (BitDFT.DescriptorPlacement.templateTape M.k) =
      (BitDFT.VectorReady.machine M).tapeOf
        ((BitDFT.VectorReady.machine M).sep :: (y.map (BitDFT.VectorReady.machine M).bitSym ++
          [(BitDFT.VectorReady.machine M).sep])))
    (htHead : c.head (BitDFT.DescriptorPlacement.templateTape M.k) = y.length+1)
    (hx : IntMul.val y+1 ≤ x.length) (out : List Bool)
    (houtput : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).cells
      (host M).outTape = fun p =>
        encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
          (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (houtputHead : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).head
      (host M).outTape = out.length+1) :
    let record := sign::x.take (IntMul.val y+1)
    let First := BitDFT.MachineSequence.native (host M)
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := BitDFT.MachineSequence.sequence
      (BitDFT.RewindTape.control (host M) (sourceTape M)) (control M)
    let q : P.K := Sum.inl (host M).qHalt
    let Post := begin_at_state P Q q
    let Stage := BitDFT.MachineSequence.sequence P Q
    let stageStart := BitDFT.MachineSequence.leftCfg P Q
      (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
        (BitDFT.RecordTerminator.control M)
        (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y))
    ∃ t1 ≤ T+6*(IntMul.val y+1)+4*y.length+7,
      ∃ u ≤ (record.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length + record.length + 7,
      ∃ v ≤ t1+1+u,
        let composed := (BitDFT.MachineSequence.sequence First Post).machine.step^[v]
          (BitDFT.MachineSequence.leftCfg First Post
            ((host M).initCfg input extra))
        composed = BitDFT.MachineSequence.rightCfg First Post
          (to_begin_at_state_cfg P Q q (Stage.machine.step^[u] stageStart)) := by
  dsimp only
  let record := sign::x.take (IntMul.val y+1)
  let b := BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y
  let First := BitDFT.MachineSequence.native (host M)
  let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
    (BitDFT.RecordTerminator.control M)
  let Q := BitDFT.MachineSequence.sequence
    (BitDFT.RewindTape.control (host M) (sourceTape M)) (control M)
  let q : P.K := Sum.inl (host M).qHalt
  let Post := begin_at_state P Q q
  let Stage := BitDFT.MachineSequence.sequence P Q
  let stageStart := BitDFT.MachineSequence.leftCfg P Q
    (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M) b)
  obtain ⟨t1,ht1,hfirst⟩ := BitDFT.first_coordinate_execution
    M c input extra T hrun hhalt rootCells rootHead sign x y hroot hrootHead hv hvHead
    hc hcHead ht htHead hx
  obtain ⟨hrecord,hrecordHead⟩ := BitDFT.first_coordinate_record_layout_for_copy
    M c rootCells rootHead sign x y hx
  have hstate : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).state =
      (host M).qHalt := by
    simp [BitDFT.FirstCoordinate.final,host,BitDFT.RecordTerminator.storage,
      BitDFT.FirstCoordinate.machine,BitDFT.FirstCoordinate.control,
      BitDFT.MachineSequence.rightCfg,BitDFT.MachineSequence.sequence,
      BitDFT.SignedBlockPlacement.embed,BitDFT.TapePermutation.embed,
      BitDFT.TapeExtension.embed,BitDFT.AlphabetEmbedding.embed,
      BitDFT.WorkRelocation.embed,BitDFT.SignedBlock.final,
      BitDFT.SignedBlock.machine,BitDFT.SignedBlock.blockControl,
      BitDFT.SignedBlock.signControl,BitDFT.SignedBlock.blockFrame,
      BitDFT.CountedBlock.frame]
  have hblank : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).cells
      (sourceTape M) ((BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).head
        (sourceTape M)) = (host M).blank := by
    rw [hrecord,hrecordHead]
    simp [BitDFT.RecordSuffixCopy.encode,MultitapeTM.tapeOf]
  obtain ⟨u,hu,hstage⟩ := BitDFT.first_coordinate_actual_terminator_rewind_copy_frame
    M c rootCells rootHead sign x y hx out houtput houtputHead
  have hfirst' : First.machine.step^[t1] (First.machine.initCfg input extra) =
      native_cfg b := by
    have hr := native_run_cfg ((host M).initCfg input extra) t1
    rw [native_init_cfg] at hr
    rw [hfirst] at hr
    exact hr
  have hhaltFirst : (First.machine.step^[t1]
      (First.machine.initCfg input extra)).state = First.exit := by
    rw [hfirst']
    simpa [First,native_cfg,host,BitDFT.RecordTerminator.storage,
      BitDFT.MachineSequence.native,b] using hstate
  have hstart : BitDFT.MachineSequence.handoff First Post
      (First.machine.step^[t1] (First.machine.initCfg input extra)) =
      to_begin_at_state_cfg P Q q stageStart := by
    rw [hfirst']
    apply cfg_ext
    · change Sum.inl q = Sum.inl (Sum.inl b.state)
      have hs : q = Sum.inl b.state := by
        dsimp [q]
        exact congrArg Sum.inl hstate.symm
      exact congrArg Sum.inl hs
    · rfl
    · rfl
  obtain ⟨v,hvbound,hseq⟩ := BitDFT.machine_sequence_bound First Post
    (First.machine.initCfg input extra) t1 u hhaltFirst
  refine ⟨t1,?_,u,?_,v,?_,?_⟩
  · exact ht1
  · exact hu
  · exact hvbound
  · have hseq' := hseq
    rw [hstart,begin_at_state_run P Q q stageStart u] at hseq'
    exact hseq'
