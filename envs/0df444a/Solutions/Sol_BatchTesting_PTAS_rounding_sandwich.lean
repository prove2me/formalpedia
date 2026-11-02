-- Prove2me | solution 1 for BatchTesting.PTAS.rounding_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:13:50.183702+00:00
-- url     : https://prove2.me/submissions/a1dbe894-086c-447f-a47b-99d7e4f4a4a6

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

open BatchTesting.PTAS

namespace BTRoundAux

theorem pow_ceil_logb (b x : ℝ) (hb : 1 < b) (hx : 1 ≤ x) :
    x ≤ b ^ ⌈Real.logb b x⌉₊ ∧ b ^ ⌈Real.logb b x⌉₊ ≤ b * x := by
  have hb0 : 0 < b := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ Real.logb b x := Real.logb_nonneg hb hx
  have hxy : b ^ Real.logb b x = x := Real.rpow_logb hb0 hb.ne' hx0
  have hk1 : Real.logb b x ≤ (⌈Real.logb b x⌉₊ : ℝ) := Nat.le_ceil _
  have hk2 : (⌈Real.logb b x⌉₊ : ℝ) < Real.logb b x + 1 := Nat.ceil_lt_add_one hy0
  rw [← Real.rpow_natCast]
  constructor
  · calc x = b ^ Real.logb b x := hxy.symm
      _ ≤ b ^ (⌈Real.logb b x⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le hb.le hk1
  · calc b ^ (⌈Real.logb b x⌉₊ : ℝ) ≤ b ^ (Real.logb b x + 1) :=
          Real.rpow_le_rpow_of_exponent_le hb.le hk2.le
      _ = b * x := by rw [Real.rpow_add hb0, hxy, Real.rpow_one]; ring

theorem cmin_pos {n : ℕ} (I : Instance n) (hI : I.Standing) : 0 < cmin I := by
  obtain ⟨hn, -, hc, -⟩ := hI
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := I.c)
  unfold cmin; rw [← hj]; exact hc j

theorem cmin_le {n : ℕ} (I : Instance n) (i : Fin n) : cmin I ≤ I.c i :=
  ciInf_le (Set.finite_range _).bddBelow i

theorem roundedCost_bounds {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps)
    (i : Fin n) : I.c i ≤ roundedCost I eps i ∧ roundedCost I eps i ≤ (1 + eps) * I.c i := by
  have hm := cmin_pos I hI
  have hx : 1 ≤ I.c i / cmin I := by rw [le_div_iff₀ hm]; simpa using cmin_le I i
  obtain ⟨h1, h2⟩ := pow_ceil_logb (1 + eps) (I.c i / cmin I) (by linarith) hx
  unfold roundedCost classOf
  constructor
  · calc I.c i = cmin I * (I.c i / cmin I) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hm.le
  · calc cmin I * (1 + eps) ^ ⌈Real.logb (1 + eps) (I.c i / cmin I)⌉₊
        ≤ cmin I * ((1 + eps) * (I.c i / cmin I)) := mul_le_mul_of_nonneg_left h2 hm.le
      _ = (1 + eps) * I.c i := by field_simp

theorem phi_nonneg {n : ℕ} (I : Instance n) (hI : I.Standing) (S : List (Finset (Fin n))) (t : ℕ) :
    0 ≤ phi I S t := by
  unfold phi
  exact Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun i _ => (hI.2.1 i).1

end BTRoundAux

open BTRoundAux in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (S : List (Finset (Fin n))) (hS : IsTestingScheme S) :
    expectedCost I S ≤ expectedCostWith I (roundedCost I eps) S ∧
      expectedCostWith I (roundedCost I eps) S ≤ (1 + eps) * expectedCost I S := by
  have hb := hI.2.2.2
  unfold expectedCost expectedCostWith
  constructor
  · apply Finset.sum_le_sum
    intro t _
    apply mul_le_mul_of_nonneg_left _ (phi_nonneg I hI S t)
    unfold batchCost
    gcongr with i _
    exact (roundedCost_bounds I hI eps h0 i).1
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    have hφ := phi_nonneg I hI S t
    have : batchCost I (roundedCost I eps) (S.getD t ∅) ≤ (1 + eps) * batchCost I I.c (S.getD t ∅) := by
      unfold batchCost
      rw [mul_add, Finset.mul_sum]
      have : I.beta ≤ (1 + eps) * I.beta := by nlinarith
      gcongr with i _
      exact (roundedCost_bounds I hI eps h0 i).2
    calc phi I S t * batchCost I (roundedCost I eps) (S.getD t ∅)
        ≤ phi I S t * ((1 + eps) * batchCost I I.c (S.getD t ∅)) := mul_le_mul_of_nonneg_left this hφ
      _ = _ := by ring
