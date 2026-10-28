-- Prove2me | solution 1 for BitDFT.rewind_then_bit_advance_to_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T05:05:20.54151+00:00
-- url     : https://prove2.me/submissions/e775569d-a00e-43e6-9d00-a4014358c770

import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_BitAdvance
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_BitAdvance_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

set_option autoImplicit false
open IntMul BitDFT BitDFT.MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem solution
    (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (p L counterHead : ℕ)
    (hcounter : base.head counter = counterHead)
    (hmarker : base.cells source 0 = N.startSym)
    (hsource : ∀ r, 0 < r → base.cells source r ≠ N.startSym)
    (hbits : ∀ r, r < L →
      base.cells counter (counterHead+r) = N.zero ∨ base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.zero ∧
      base.cells counter (counterHead+L) ≠ N.one) :
    ∃ t : ℕ, t ≤ p + L + 3 ∧
      (MachineSequence.sequence (BitDFT.RewindTape.control N source)
        (BitDFT.BitAdvance.control N source counter hsc)).machine.step^[t]
        (MachineSequence.leftCfg (BitDFT.RewindTape.control N source)
          (BitDFT.BitAdvance.control N source counter hsc)
          (BitDFT.RewindTape.frame N source base false p)) =
      MachineSequence.rightCfg (BitDFT.RewindTape.control N source)
        (BitDFT.BitAdvance.control N source counter hsc)
        (BitDFT.BitAdvance.frame N source counter hsc base true (L+1)
          (counterHead+L)) := by
  let P := BitDFT.RewindTape.control N source
  let Q := BitDFT.BitAdvance.control N source counter hsc
  let c₀ := BitDFT.RewindTape.frame N source base false p
  have hrew := BitDFT.rewind_tape_correct N source base hmarker hsource p
  have hhalt : (P.machine.step^[p+1] c₀).state = P.exit := by
    rw [hrew]
    rfl
  obtain ⟨t, ht, hseq⟩ := BitDFT.machine_sequence_bound P Q c₀ (p+1) (L+1) hhalt
  have hhandoff : MachineSequence.handoff P Q
      (BitDFT.RewindTape.frame N source base true 1) =
      BitDFT.BitAdvance.frame N source counter hsc base false 1 counterHead := by
    apply cfg_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i = counter
      · subst i
        have hci : counter ≠ source := Ne.symm hsc
        simp [MachineSequence.handoff, BitDFT.RewindTape.frame,
          BitDFT.BitAdvance.frame, Function.update, hci, hcounter]
      · simp [MachineSequence.handoff, BitDFT.RewindTape.frame,
          BitDFT.BitAdvance.frame, Function.update, hi, hcounter]
  have hadv := BitDFT.BitAdvance.correct N source counter hsc base L 1
    counterHead hbits hstop
  rw [hrew, hhandoff, hadv] at hseq
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa [P, Q, c₀, Nat.add_comm] using hseq
