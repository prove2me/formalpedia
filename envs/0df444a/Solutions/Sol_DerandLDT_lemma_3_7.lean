-- Prove2me | solution 1 for DerandLDT.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:13:14.197096+00:00
-- url     : https://prove2.me/submissions/04ddd3a5-7cfa-49fa-bd8a-2aeb8080b538

import Mathlib

universe u

open Polynomial

theorem solution (F : Type u) [Field F] (p : ℕ) [CharP F p] :
    (∀ f : F[X], f ≠ 0 → 1 ≤ f.natDegree →
      (hasseDeriv 1 f = 0 ↔ ∃ g : F[X], expand F p g = f)) ∧
    (∀ f g : F[X], hasseDeriv 1 (f * g) = g * hasseDeriv 1 f + f * hasseDeriv 1 g) ∧
    (∀ (f : F[X]) (n : ℕ), hasseDeriv 1 (f ^ n) = (n : F[X]) * f ^ (n - 1) * hasseDeriv 1 f) := by
  refine ⟨fun f hf hdeg => ?_, fun f g => ?_, fun f n => ?_⟩
  · rw [hasseDeriv_one']
    constructor
    · intro hd
      rcases Nat.eq_zero_or_pos p with hp0 | hppos
      · -- characteristic zero: derivative zero forces a constant
        subst hp0
        haveI : CharZero F := CharP.charP_to_charZero F
        have := natDegree_eq_zero_of_derivative_eq_zero hd
        omega
      · exact ⟨contract p f, expand_contract p hd hppos.ne'⟩
    · rintro ⟨g, rfl⟩
      rw [derivative_expand]
      have : (p : F[X]) = 0 := by
        rw [← map_natCast (C : F →+* F[X]), CharP.cast_eq_zero, map_zero]
      rw [this]; simp
  · rw [hasseDeriv_one', hasseDeriv_one', hasseDeriv_one', derivative_mul]; ring
  · rw [hasseDeriv_one', hasseDeriv_one', derivative_pow, ← C_eq_natCast]
