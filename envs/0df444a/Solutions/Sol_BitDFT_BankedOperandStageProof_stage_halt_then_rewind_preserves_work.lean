-- Prove2me | solution 1 for BitDFT.BankedOperandStageProof.stage_halt_then_rewind_preserves_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:52:53.303894+00:00
-- url     : https://prove2.me/submissions/3bf7d847-93ae-4167-932e-f2aaabf6c44a

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_BankedOperandStageProof_stage_halt_then_rewind
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open IntMul BitDFT.MachineSequence

private theorem rewind_frame_head_other {N : MultitapeTM}
    (j i : Fin N.k) (base : N.Cfg) (q : Bool) (p : ℕ)
    (hne : i ≠ j) :
    (BitDFT.RewindTape.frame N j base q p).head i = base.head i := by
  simp [BitDFT.RewindTape.frame, Function.update_of_ne hne]

theorem solution
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
        (BitDFT.MachineSequence.leftCfg P Q c) = BitDFT.MachineSequence.rightCfg P Q rf ∧
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
            exact rewind_frame_head_other out
              (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i)
              ⟨N.qStart, c.cells, c.head⟩ true 1 hne
        _ = 1 := hw.2
end
