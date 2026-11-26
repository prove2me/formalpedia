-- Prove2me | solution 1 for Erdos287.large_square_divisor_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:28:59.079411+00:00
-- url     : https://prove2.me/submissions/38f5f548-751c-40c1-a7a1-b9dc2787f6cc

import Mathlib

open Finset

set_option autoImplicit false

/-- The weighted contribution of numbers divisible by the square of an integer larger than `U`. -/
theorem solution (X U : ℕ) (hU : 0 < U) (w : ℕ → ℝ) :
    let E := (Finset.Ioc 0 X).filter (fun n => ∃ p ∈ Finset.Ioc U X, p ^ 2 ∣ n)
    (E.card : ℝ) ≤ (X : ℝ) / U ∧
      (∑ n ∈ E, w n) ^ 2 ≤ ((X : ℝ) / U) * ∑ n ∈ Finset.Ioc 0 X, w n ^ 2 := by
  classical
  let E := (Ioc 0 X).filter (fun n => ∃ p ∈ Ioc U X, p ^ 2 ∣ n)
  let A (p : ℕ) := (Ioc 0 X).filter (fun n => p ^ 2 ∣ n)
  have hcover : E ⊆ (Ioc U X).biUnion A := by
    intro n hn
    obtain ⟨hnI, p, hp, hpn⟩ := mem_filter.mp hn
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hnI, hpn⟩⟩
  have hcard : (E.card : ℝ) ≤ (X : ℝ) / U := by
    calc
      _ ≤ ∑ p ∈ Ioc U X, ((A p).card : ℝ) := by
        exact_mod_cast (card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ p ∈ Ioc U X, (X : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro p hp
        simp only [A, Nat.Ioc_filter_dvd_card_eq_div, ← div_eq_mul_inv]
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hU.trans (mem_Ioc.mp hp).1
        apply (le_div_iff₀ (sq_pos_of_pos hp0)).mpr
        exact_mod_cast Nat.div_mul_le_self X (p ^ 2)
      _ = (X : ℝ) * ∑ p ∈ Ioc U X, ((p : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
      _ ≤ (X : ℝ) / U := by
        rw [div_eq_mul_inv]
        gcongr
        by_cases hUX : U ≤ X
        · exact (sum_Ioc_inv_sq_le_sub hU.ne' hUX).trans (sub_le_self _ (by positivity))
        · rw [Ioc_eq_empty_of_le (Nat.le_of_not_ge hUX), sum_empty]
          positivity
  refine ⟨hcard, ?_⟩
  have hcs : (∑ n ∈ E, w n) ^ 2 ≤ (E.card : ℝ) * ∑ n ∈ E, w n ^ 2 := by
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
      (sum_mul_sq_le_sq_mul_sq E (fun _ => (1 : ℝ)) w)
  exact hcs.trans (mul_le_mul hcard
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _))
    (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))

