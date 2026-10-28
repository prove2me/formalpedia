-- Prove2me | solution 1 for BitDFT.BitAdvance.correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T05:01:08.785997+00:00
-- url     : https://prove2.me/submissions/a14728f7-a727-49e9-892a-01fb24d10cbd

import Definitions.Def_BitDFT_BitAdvance
import Mathlib.Tactic

open IntMul BitDFT.BitAdvance

private theorem cfg_ext {N : MultitapeTM} {source counter : Fin N.k}
    {hsc : source ≠ counter}
    (c d : (machine N source counter hsc).Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem run_continue (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (sourceHead counterHead : ℕ)
    (hbit : base.cells counter counterHead = N.zero ∨ base.cells counter counterHead = N.one) :
    (machine N source counter hsc).step
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base false (sourceHead+1) (counterHead+1) := by
  cases base with
  | mk state cells head =>
    let c0 := frame N source counter hsc ⟨state, cells, head⟩ false sourceHead counterHead
    have hscanSimple : cells counter counterHead = N.zero ∨ cells counter counterHead = N.one := by simpa using hbit
    have hscan : cells counter
        (Function.update (Function.update head source sourceHead) counter counterHead counter) = N.zero ∨
        cells counter (Function.update (Function.update head source sourceHead) counter counterHead counter) = N.one := by
      simp [Function.update, hsc, hscanSimple]
    apply cfg_ext
    · simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
    · funext i p
      by_cases hiS : i = source
      · subst i
        simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
      · by_cases hiC : i = counter
        · subst i
          simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
        · simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hiS, hiC]
    · funext i
      by_cases hiS : i = source
      · subst i
        simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
      · by_cases hiC : i = counter
        · subst i
          simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
        · simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hiS, hiC]

private theorem run_stop (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (sourceHead counterHead : ℕ)
    (hstop : base.cells counter counterHead ≠ N.zero ∧ base.cells counter counterHead ≠ N.one) :
    (machine N source counter hsc).step
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base true sourceHead counterHead := by
  cases base with
  | mk state cells head =>
    have hstop' : cells counter counterHead ≠ N.zero ∧ cells counter counterHead ≠ N.one := by simpa using hstop
    apply cfg_ext
    · simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, frame, Function.update, hstop']
    · funext i p
      by_cases hiS : i = source
      · subst i
        simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, frame, Function.update, hstop']
      · by_cases hiC : i = counter
        · subst i
          simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, frame, Function.update, hstop']
        · simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, frame, Function.update, hiS, hiC, hstop']
    · funext i
      by_cases hiS : i = source
      · subst i
        simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, frame, Function.update, hstop']
      · by_cases hiC : i = counter
        · subst i
          simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, frame, Function.update, hstop']
        · simp [machine, BitDFT.BitAdvance.control, MultitapeTM.step, transition, frame, Function.update, hiS, hiC, hstop']

theorem solution (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (L sourceHead counterHead : ℕ)
    (hbits : ∀ r, r < L →
      base.cells counter (counterHead+r) = N.zero ∨ base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.zero ∧
      base.cells counter (counterHead+L) ≠ N.one) :
    (machine N source counter hsc).step^[L+1]
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base true (sourceHead+L) (counterHead+L) := by
  induction L generalizing sourceHead counterHead with
  | zero =>
      have hs := run_stop N source counter hsc base sourceHead counterHead (by simpa using hstop)
      simpa using hs
  | succ L ih =>
      have hfirst := run_continue N source counter hsc base sourceHead counterHead (hbits 0 (by omega))
      have htail : ∀ r, r < L →
          base.cells counter (counterHead+1+r) = N.zero ∨ base.cells counter (counterHead+1+r) = N.one := by
        intro r hr
        have h := hbits (r+1) (by omega)
        have heq : counterHead+1+r = counterHead+(r+1) := by omega
        rw [heq]
        exact h
      have hlast : base.cells counter (counterHead+1+L) ≠ N.zero ∧
          base.cells counter (counterHead+1+L) ≠ N.one := by
        have heq : counterHead+1+L = counterHead+(L+1) := by omega
        rw [heq]
        exact hstop
      rw [show L+1+1 = (L+1)+1 by omega, Function.iterate_succ_apply]
      rw [hfirst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (sourceHead+1) (counterHead+1) htail hlast
