-- Prove2me | solution 1 for BitDFT.ReaderOutputStageRun.reader_outputs_stage_rewound_with_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T19:04:02.760647+00:00
-- url     : https://prove2.me/submissions/61b8260b-550c-4645-922e-4795fc3f41dd

import Definitions.Def_BitDFT_ReaderOutputStageSupport
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_halt_with_work_v2
import Theorems.Thm_BitDFT_BankedOperandStageProof_stage_halt_then_rewind
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.MachineSequence

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

private theorem rewind_preserves_staged_work
    (A M H : MultitapeTM) (j : Fin A.k) (hj : 1 ≤ j.val)
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
    (c : (BitDFT.BankedOperandStage.controller A M H j hj).machine.Cfg)
    (hs : c.state = BitDFT.OperandStage.State.halt)
    (p : ℕ) (hp : c.head (BitDFT.BankedOperandStage.multiplierOutputTape A M H) = p)
    (hmarker : c.cells (BitDFT.BankedOperandStage.multiplierOutputTape A M H) 0 =
      (BitDFT.ReaderHostFrame.host A M H).startSym)
    (hnomarker : ∀ i, 0 < i →
      c.cells (BitDFT.BankedOperandStage.multiplierOutputTape A M H) i ≠
        (BitDFT.ReaderHostFrame.host A M H).startSym)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      c.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) =
        (BitDFT.ReaderHostFrame.host A M H).tapeOf [] ∧
      c.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) :
    let N := BitDFT.ReaderHostFrame.host A M H
    let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
    let P := BitDFT.BankedOperandStage.controller A M H j hj
    let Q := BitDFT.RewindTape.control N out
    let rf := BitDFT.RewindTape.frame N out ⟨N.qStart, c.cells, c.head⟩ true 1
    ∃ v ≤ p + 2,
      (BitDFT.MachineSequence.sequence P Q).machine.step^[v]
        (BitDFT.MachineSequence.leftCfg P Q c) =
          BitDFT.MachineSequence.rightCfg P Q rf ∧
      ∀ i : Fin (M.k + 2), 2 ≤ i.val →
        rf.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
        rf.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1 := by
  let N := BitDFT.ReaderHostFrame.host A M H
  let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
  let P := BitDFT.BankedOperandStage.controller A M H j hj
  let Q := BitDFT.RewindTape.control N out
  obtain ⟨v, hv, hrun⟩ :=
    BitDFT.BankedOperandStageProof.stage_halt_then_rewind
      (N := N) (BitDFT.BankedOperandStage.coordinateTape A M H j)
      (BitDFT.BankedOperandStage.dimensionTape A M H) out hc hd ho hcd hco hdo
      c hs p hp hmarker hnomarker
  refine ⟨v, hv, ?_, ?_⟩
  · simpa [P, Q, N, out, BitDFT.BankedOperandStage.controller] using hrun
  · intro i hi
    have haddr := BitDFT.DedicatedTapeBanks.multiplier_work_address A
      (BitDFT.ReaderHostFrame.tracked M) H i (by omega)
    have hroute : (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i).val =
        A.k + i.val - 1 := by
      have hv' := congrArg Fin.val haddr
      simpa [BitDFT.ReaderHostFrame.multiplierTapeRoute,
        BitDFT.ReaderHostFrame.tracked, BitDFT.BankedTripleAlphabetHost.route,
        BitDFT.TapeExtension.oldTape, Fin.cast] using hv'
    have hout : out.val = A.k := rfl
    have hne : BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i ≠ out := by
      intro he
      have hv' := congrArg Fin.val he
      rw [hroute, hout] at hv'
      omega
    have hw := hwork i hi
    constructor
    · simpa [BitDFT.RewindTape.frame, N, out, hne] using hw.1
    · change (BitDFT.RewindTape.frame N out
        ⟨N.qStart, c.cells, c.head⟩ true 1).head
          (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1
      calc
        (BitDFT.RewindTape.frame N out ⟨N.qStart, c.cells, c.head⟩ true 1).head
            (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) =
          c.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) := by
            simp [BitDFT.RewindTape.frame]
            exact Function.update_of_ne hne 1 c.head
        _ = 1 := hw.2

theorem solution
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
    ∃ base : (BitDFT.BankedOperandStage.controller A M H j hj).machine.Cfg,
      base.cells dim = N.tapeOf (dimension.map N.bitSym) ∧
      base.head dim = dimension.length + 1 ∧
      base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) ∧
      base.head coord = low.length + 3 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
        base.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) ∧
      ∃ final : (BitDFT.BankedOperandStage.controller A M H j hj).machine.Cfg,
        (BitDFT.BankedOperandStage.controller A M H j hj).machine.step ^[
          2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo
            base ([sign, high] ++ low)) = final ∧
        final.state = BitDFT.OperandStage.State.halt ∧
        final.cells out = N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) ∧
        ∃ v ≤ final.head out + 2,
          (BitDFT.MachineSequence.sequence
            (BitDFT.BankedOperandStage.controller A M H j hj)
            (BitDFT.RewindTape.control N out)).machine.step^[v]
            (BitDFT.MachineSequence.leftCfg
              (BitDFT.BankedOperandStage.controller A M H j hj)
              (BitDFT.RewindTape.control N out) final) =
            BitDFT.MachineSequence.rightCfg
              (BitDFT.BankedOperandStage.controller A M H j hj)
              (BitDFT.RewindTape.control N out)
              (BitDFT.RewindTape.frame N out ⟨N.qStart, final.cells, final.head⟩ true 1) ∧
          ∀ i : Fin (M.k + 2), 2 ≤ i.val →
            (BitDFT.RewindTape.frame N out
              ⟨N.qStart, final.cells, final.head⟩ true 1).cells
                (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
            (BitDFT.RewindTape.frame N out
              ⟨N.qStart, final.cells, final.head⟩ true 1).head
                (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1 := by
  dsimp
  obtain ⟨base, hdCells, hdHead, hcCells, hcHead, hworkBase,
    final, hrun, hstate, hout, hworkFinal⟩ :=
      BitDFT.ReaderOutputStageRun.reader_outputs_stage_halt_with_work_v2
        A M H hH4 cF cH j hj dimension low sign high hcoord hdim hdimHead hq
        hc hd ho hcd hco hdo hpad hdimBlank
  let N := BitDFT.ReaderHostFrame.host A M H
  let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
  let dim := BitDFT.BankedOperandStage.dimensionTape A M H
  let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
  have hmarker : final.cells out 0 = N.startSym := by rw [hout]; rfl
  have hnomarker : ∀ i, 0 < i → final.cells out i ≠ N.startSym := by
    intro i hi
    rw [hout]
    exact staged_payload_no_marker dimension low i hi
  obtain ⟨v, hv, hrew, hrewWork⟩ :=
    rewind_preserves_staged_work
      A M H j hj hc hd ho hcd hco hdo final hstate (final.head out) rfl
      hmarker hnomarker hworkFinal
  refine ⟨base, hdCells, hdHead, hcCells, hcHead, hworkBase,
    final, hrun, hstate, hout, ?_⟩
  exact ⟨v, hv, by simpa [N, out, coord, dim] using hrew, hrewWork⟩
end
