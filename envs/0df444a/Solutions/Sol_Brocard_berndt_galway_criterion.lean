-- Prove2me | solution 1 for Brocard.berndt_galway_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-01T02:31:06.908346+00:00
-- url     : https://prove2.me/submissions/76f905db-e6ea-46d3-8f98-5ffbd69adcd6

import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.LegendreSymbol.Basic


theorem solution (n p : ℕ) [Fact p.Prime] (hn : n < p)
    (h : legendreSym p (((p - 1).descFactorial (p - 1 - n) : ℤ) *
      (((p - 1).descFactorial (p - 1 - n) : ℤ) - 1)) = -1)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  have hfac : n.factorial * (p - 1).descFactorial (p - 1 - n) = (p - 1).factorial := by
    have := Nat.factorial_mul_descFactorial (show p - 1 - n ≤ p - 1 by omega)
    rwa [show p - 1 - (p - 1 - n) = n by omega] at this
  have hw : (n.factorial : ZMod p) * ((p - 1).descFactorial (p - 1 - n) : ZMod p) = -1 := by
    rw [← Nat.cast_mul, hfac]
    exact ZMod.wilsons_lemma (p := p)
  have hm' : (n.factorial : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ZMod p)) hm
  rw [legendreSym.eq_neg_one_iff] at h
  apply h
  refine ⟨((p - 1).descFactorial (p - 1 - n) : ZMod p) * (m : ZMod p), ?_⟩
  push_cast
  linear_combination ((p - 1).descFactorial (p - 1 - n) : ZMod p) ^ 2 * hm' -
    ((p - 1).descFactorial (p - 1 - n) : ZMod p) * hw

