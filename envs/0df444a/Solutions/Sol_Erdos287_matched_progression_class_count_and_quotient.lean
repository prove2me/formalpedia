-- Prove2me | solution 1 for Erdos287.matched_progression_class_count_and_quotient
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:43:12.220601+00:00
-- url     : https://prove2.me/submissions/2b183bc0-0ff8-4515-a4dd-36957dd17dab

import Mathlib

set_option autoImplicit false

/-- When the outer progression is matched, there are exactly `q` choices
of the inner residue, and fixing one choice fixes the quotient modulo `q`. -/
theorem solution (b q n : ℕ) (hb : 0 < b) :
    ((Finset.range (b * q)).filter (fun a => a ≡ n [MOD b])).card = q ∧
    ∀ (p x x' s s' : ℤ), p - x = (b : ℤ) * s → p - x' = (b : ℤ) * s' →
      x ≡ x' [ZMOD (b : ℤ) * q] → s ≡ s' [ZMOD q] := by
  constructor
  · rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hb]
    simp [hb.ne']
  · intro p x x' s s' h h' hmod
    have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    apply Int.ModEq.mul_left_cancel' hb0
    rw [← h, ← h']
    exact (Int.ModEq.refl p).sub hmod

