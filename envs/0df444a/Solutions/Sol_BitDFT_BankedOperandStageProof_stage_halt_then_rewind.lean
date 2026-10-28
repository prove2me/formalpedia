-- Prove2me | solution 1 for BitDFT.BankedOperandStageProof.stage_halt_then_rewind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T15:30:06.699678+00:00
-- url     : https://prove2.me/submissions/52415a87-5543-4679-87b0-ea42e521458c

import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedOperandStageProof
open IntMul BitDFT BitDFT.MachineSequence

private theorem cfg_ext' {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) :
    c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

/-- After operand staging halts with the output head at `p`, dispatch to the
    accepted marker-rewind controller. Its result has the caller's required
    buffer head at cell one. -/
theorem stage_halt_then_rewind {N : MultitapeTM}
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
    apply cfg_ext'
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


end BitDFT.BankedOperandStageProof
end


noncomputable section
open IntMul BitDFT.MachineSequence
theorem solution {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = BitDFT.OperandStage.State.halt)
    (p : ℕ) (hp : c.head out = p)
    (hmarker : c.cells out 0 = N.startSym)
    (hnomarker : ∀ i, 0 < i → c.cells out i ≠ N.startSym) :
    ∃ v ≤ p + 2,
      (BitDFT.MachineSequence.sequence
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
        (BitDFT.RewindTape.control N out)).machine.step^[v]
        (BitDFT.MachineSequence.leftCfg
          (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
          (BitDFT.RewindTape.control N out) c) =
      BitDFT.MachineSequence.rightCfg
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
        (BitDFT.RewindTape.control N out)
        (BitDFT.RewindTape.frame N out
          ⟨N.qStart, c.cells, c.head⟩ true 1) := by
  exact BitDFT.BankedOperandStageProof.stage_halt_then_rewind (N := N) coord dim out hc hd ho hcd hco hdo c hs p hp hmarker hnomarker
end
