-- Prove2me | solution 1 for Erdos287.additive_character_subset_sum_coverage
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:04:47.847283+00:00
-- url     : https://prove2.me/submissions/3a16d4d0-b1ff-47d0-9327-02543e012c05

import Mathlib

set_option autoImplicit false

/-- A bound on the nonzero additive frequencies guarantees that every
residue is the sum of a subset of the given weights. -/
theorem solution (q : ℕ) [NeZero q] (D : Finset ℕ) (w : ℕ → ZMod q)
    (t : ZMod q)
    (hsmall : (∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
      ‖∏ n ∈ D, (1 + ZMod.stdAddChar (a * w n))‖) < (2 : ℝ) ^ D.card) :
    ∃ T ⊆ D, (∑ n ∈ T, w n) = t := by
  classical
  let χ := ZMod.stdAddChar (N := q)
  let g (a : ZMod q) := ∏ n ∈ D, (1 + χ (a * w n))
  let f (a : ZMod q) := χ (a * (-t)) * g a
  have hprod (a : ZMod q) (T : Finset ℕ) :
      (∏ n ∈ T, χ (a * w n)) = χ (∑ n ∈ T, a * w n) := by
    induction T using Finset.induction_on with
    | empty => simp [χ, AddChar.map_zero_eq_one]
    | insert n T hn ih =>
      rw [Finset.prod_insert hn, Finset.sum_insert hn, ih, AddChar.map_add_eq_mul]
  have hexpand (a : ZMod q) :
      f a = ∑ T ∈ D.powerset, χ (a * ((∑ n ∈ T, w n) - t)) := by
    change χ (a * (-t)) * (∏ n ∈ D, (1 + χ (a * w n))) = _
    rw [Finset.prod_one_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [hprod, ← AddChar.map_add_eq_mul, ← Finset.mul_sum, ← mul_add, add_comm, sub_eq_add_neg]
  by_contra hnone
  have hsum : (∑ a : ZMod q, f a) = 0 := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro T hT
    have hne : (∑ n ∈ T, w n) - t ≠ 0 := by
      intro he
      exact hnone ⟨T, Finset.mem_powerset.mp hT, sub_eq_zero.mp he⟩
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), if_neg hne]
    exact Nat.cast_zero
  have hfzero : f 0 = (2 : ℂ) ^ D.card := by
    simp [f, g, χ, AddChar.map_zero_eq_one, one_add_one_eq_two]
  have hnonzero : (∑ a ∈ Finset.univ.erase (0 : ZMod q), f a) = -(2 : ℂ) ^ D.card := by
    apply eq_neg_of_add_eq_zero_left
    rw [← hfzero, Finset.sum_erase_add _ _ (Finset.mem_univ _), hsum]
  have hnorm (a : ZMod q) : ‖f a‖ = ‖g a‖ := by
    simp [f, χ, ZMod.stdAddChar_apply, Circle.norm_coe]
  have hbound := norm_sum_le (Finset.univ.erase (0 : ZMod q)) f
  rw [hnonzero] at hbound
  simp only [norm_neg, norm_pow, Complex.norm_ofNat, hnorm] at hbound
  exact (not_lt_of_ge hbound) hsmall

