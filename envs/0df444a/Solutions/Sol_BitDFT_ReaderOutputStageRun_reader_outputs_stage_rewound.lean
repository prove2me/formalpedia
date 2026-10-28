-- Prove2me | solution 1 for BitDFT.ReaderOutputStageRun.reader_outputs_stage_rewound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T17:06:20.700556+00:00
-- url     : https://prove2.me/submissions/3c5c376a-9478-4357-85bd-f8fdb7a0b240

import Definitions.Def_BitDFT_ReaderOutputStageRun
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence

namespace BitDFT.ReaderOutputStageRun

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem stage_halt_then_rewind {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = BitDFT.OperandStage.State.halt)
    (p : ℕ) (hp : c.head out = p)
    (hmarker : c.cells out 0 = N.startSym)
    (hnomarker : ∀ i, 0 < i → c.cells out i ≠ N.startSym) :
    ∃ v ≤ p + 2,
      (MachineSequence.sequence
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
        (BitDFT.RewindTape.control N out)).machine.step^[v]
        (MachineSequence.leftCfg
          (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
          (BitDFT.RewindTape.control N out) c) =
      MachineSequence.rightCfg
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
        (BitDFT.RewindTape.control N out)
        (BitDFT.RewindTape.frame N out
          ⟨N.qStart, c.cells, c.head⟩ true 1) := by
  let P := BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo
  let Q := BitDFT.RewindTape.control N out
  let base : N.Cfg := ⟨N.qStart, c.cells, c.head⟩
  have hh : MachineSequence.handoff P Q c =
      BitDFT.RewindTape.frame N out base false p := by
    apply cfg_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i = out
      · subst i
        simp [MachineSequence.handoff, BitDFT.RewindTape.frame, base, hp]
      · simp [MachineSequence.handoff, BitDFT.RewindTape.frame, base, hi]
  have hrew := BitDFT.rewind_tape_correct N out base hmarker hnomarker p
  have hexit : ((P.machine.step^[0]) c).state = P.exit := by
    change c.state = P.exit
    simpa [P, BitDFT.OperandStage.control] using hs
  obtain ⟨v, hv, hrun⟩ := BitDFT.machine_sequence_bound P Q c 0 (p + 1) hexit
  refine ⟨v, ?_, ?_⟩
  · omega
  · rw [show P.machine.step^[0] c = c by rfl, hh, hrew] at hrun
    simpa [P, Q, base] using hrun

private theorem bit_ne_start {N : MultitapeTM} (b : Bool) :
    N.bitSym b ≠ N.startSym := by
  cases b <;> simp [MultitapeTM.bitSym]
  all_goals
    have hd := N.syms_distinct
    simp only [List.nodup_cons, List.mem_cons, not_or] at hd
    first | exact Ne.symm hd.2.1.1 | exact Ne.symm hd.2.1.2.1

private theorem sep_ne_start {N : MultitapeTM} : N.sep ≠ N.startSym := by
  intro h
  have hnot := (List.nodup_cons.mp N.syms_distinct).2
  have hnot := (List.nodup_cons.mp hnot).1
  exact hnot (by simp [h])

private theorem getD_not_start {N : MultitapeTM} (w : List N.Sym)
    (d : N.Sym) (hd : d ≠ N.startSym)
    (hall : ∀ s ∈ w, s ≠ N.startSym) (i : ℕ) :
    w.getD i d ≠ N.startSym := by
  induction w generalizing i with
  | nil => simp [List.getD, hd]
  | cons a w ih =>
    cases i with
    | zero => simpa [List.getD] using hall a (by simp)
    | succ i =>
      simpa [List.getD] using ih (by
        intro s hs
        exact hall s (by simp [hs])) i

private theorem staged_payload_no_marker {N : MultitapeTM}
    (dimension low : List Bool) :
    ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank ::
        (List.replicate (low.length - dimension.length) N.zero ++
          dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym))) p ≠ N.startSym := by
  intro p hp
  have hblank : N.blank ≠ N.startSym := by
    intro h
    exact (List.nodup_cons.mp N.syms_distinct).1 (by simp [h])
  have hzero : N.zero ≠ N.startSym := by
    intro h
    have hnot := (List.nodup_cons.mp N.syms_distinct).2
    have hnot := (List.nodup_cons.mp hnot).1
    exact hnot (by simp [h])
  have hpayload : ∀ s ∈ (List.replicate (low.length - dimension.length) N.zero ++
      dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym), s ≠ N.startSym := by
    intro s hs
    change s ∈ (((List.replicate (low.length - dimension.length) N.zero ++
      dimension.map N.bitSym) ++ [N.sep]) ++ low.map N.bitSym) at hs
    rcases List.mem_append.mp hs with hleft | hlow
    · rcases List.mem_append.mp hleft with hleft | hsep
      · rcases List.mem_append.mp hleft with hrep | hdim
        · simp only [List.mem_replicate] at hrep
          exact hrep.2 ▸ hzero
        · rcases List.mem_map.mp hdim with ⟨b, _, hbs⟩
          rw [← hbs]
          exact bit_ne_start b
      · simp only [List.mem_singleton] at hsep
        rw [hsep]
        exact sep_ne_start
    · rcases List.mem_map.mp hlow with ⟨b, _, hbs⟩
      rw [← hbs]
      exact bit_ne_start b
  cases p with
  | zero => omega
  | succ p =>
    change (N.blank ::
      (List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
        [N.sep] ++ low.map N.bitSym)).getD p N.blank ≠ N.startSym
    cases p with
    | zero => simpa [List.getD] using hblank
    | succ p =>
      simpa [List.getD] using getD_not_start
        (List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
          [N.sep] ++ low.map N.bitSym) N.blank hblank hpayload p

/-- The actual reader output can be staged, halted, and rewound to the
    tracked-call convention while retaining the exact padded operand payload. -/
theorem reader_outputs_stage_rewound_proof
    (A M H : MultitapeTM) (hH4 : 3 < H.k)
    (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k) (hj : 1 ≤ j.val)
    (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1)
    (hq : dimension.length ≤ low.length)
    (hc : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (hd : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (ho : BitDFT.BankedOperandStage.multiplierOutputTape A M H ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (hcd : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.dimensionTape A M H)
    (hco : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (hdo : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (hpad : ∀ p, 1 ≤ p →
      ((BitDFT.ReaderHostFrame.host A M H).tapeOf
        ((BitDFT.ReaderHostFrame.host A M H).blank ::
          List.replicate low.length (BitDFT.ReaderHostFrame.host A M H).zero)) p ≠
          (BitDFT.ReaderHostFrame.host A M H).startSym)
    (hdimBlank : ((BitDFT.ReaderHostFrame.host A M H).tapeOf
      (dimension.map (BitDFT.ReaderHostFrame.host A M H).bitSym))
        (dimension.length + 1) = (BitDFT.ReaderHostFrame.host A M H).blank) :
    let N := BitDFT.ReaderHostFrame.host A M H
    let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
    let dim := BitDFT.BankedOperandStage.dimensionTape A M H
    let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
    ∃ base : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
      base.cells dim = N.tapeOf (dimension.map N.bitSym) ∧
      base.head dim = dimension.length + 1 ∧
      base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) ∧
      base.head coord = low.length + 3 ∧
      ∃ final : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
          2 * dimension.length + 3 * low.length + 14]
          (@entryFrame N coord dim out hc hd ho hcd hco hdo base ([sign, high] ++ low)) = final ∧
        final.state = BitDFT.OperandStage.State.halt ∧
        final.cells out = N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) ∧
        ∃ v ≤ final.head out + 2,
          (MachineSequence.sequence
            (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
            (BitDFT.RewindTape.control N out)).machine.step^[v]
            (MachineSequence.leftCfg
              (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
              (BitDFT.RewindTape.control N out) final) =
            MachineSequence.rightCfg
              (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
              (BitDFT.RewindTape.control N out)
              (BitDFT.RewindTape.frame N out
                ⟨N.qStart, final.cells, final.head⟩ true 1) := by
  dsimp
  let N := BitDFT.ReaderHostFrame.host A M H
  let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
  let dim := BitDFT.BankedOperandStage.dimensionTape A M H
  let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
  let P := BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo
  obtain ⟨base, hdCells, hdHead, hcCells, hcHead⟩ :=
    BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame
      A M H hH4 cF cH j hj dimension low sign high hcoord hdim hdimHead
  have hrun := BitDFT.BankedOperandStageProof.coordinate_pair_to_halt
    coord dim out hc hd ho hcd hco hdo base dimension low sign high
    hdCells hdHead hcCells hcHead hq hpad hdimBlank
  have hbuffer := BitDFT.BankedOperandStageProof.coordinate_pair_output_buffer
    coord dim out hc hd ho hcd hco hdo base dimension low sign high
    hdCells hdHead hcCells hcHead hq hpad hdimBlank
  let final : P.machine.Cfg :=
      ⟨BitDFT.OperandStage.State.halt,
        (BitDFT.BankedOperandStageProofSupport.coordinateCopyFrame coord dim out hc hd ho hcd hco hdo
          base ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
            [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
            [N.sep]).length + low.length + 2)).cells,
        (BitDFT.BankedOperandStageProofSupport.coordinateCopyFrame coord dim out hc hd ho hcd hco hdo
          base ([sign, high] ++ low)
          (List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
            [N.sep] ++ low.map N.bitSym)
          (low.length + 3)
          ((List.replicate (low.length - dimension.length) N.zero ++ dimension.map N.bitSym ++
            [N.sep]).length + low.length + 2)).head⟩
  have hEntry : @entryFrame N coord dim out hc hd ho hcd hco hdo base
      ([sign, high] ++ low) =
      @BitDFT.BankedOperandStageProofSupport.initialStageFrame N coord dim out hc hd ho hcd hco hdo
        base ([sign, high] ++ low) := by rfl
  have hrun' : P.machine.step^[2 * dimension.length + 3 * low.length + 14]
      (@entryFrame N coord dim out hc hd ho hcd hco hdo base ([sign, high] ++ low)) = final := by
    rw [hEntry]
    simpa [final] using hrun
  have hstate : final.state = BitDFT.OperandStage.State.halt := by rfl
  have hout : final.cells out = N.tapeOf (N.blank ::
      (List.replicate (low.length - dimension.length) N.zero ++
        dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) := by
    rw [← hrun']
    change (P.machine.step^[2 * dimension.length + 3 * low.length + 14]
      (@entryFrame N coord dim out hc hd ho hcd hco hdo base ([sign, high] ++ low))).cells out = _
    rw [hEntry]
    simpa [BitDFT.BankedOperandStageProofSupport.coordinateCopyFrame, hco, hdo] using hbuffer
  have hmarker : final.cells out 0 = N.startSym := by rw [hout]; rfl
  have hnomarker : ∀ i, 0 < i → final.cells out i ≠ N.startSym := by
    intro i hi
    rw [hout]
    exact staged_payload_no_marker dimension low i hi
  obtain ⟨v, hv, hrew⟩ := stage_halt_then_rewind (N := N)
    coord dim out hc hd ho hcd hco hdo
    final hstate (final.head out) rfl hmarker hnomarker
  refine ⟨base, hdCells, hdHead, hcCells, hcHead, final, hrun, hstate, hout, ?_⟩
  exact ⟨v, hv, hrew⟩

end BitDFT.ReaderOutputStageRun
end

abbrev solution := @BitDFT.ReaderOutputStageRun.reader_outputs_stage_rewound_proof
