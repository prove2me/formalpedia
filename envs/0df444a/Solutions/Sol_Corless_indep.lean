-- Prove2me | solution 1 for Corless.indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:37.706267+00:00
-- url     : https://prove2.me/submissions/add65ac9-d1bf-45b1-9e74-e52da3dce03b

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_coeff_P_zero
public import Theorems.Thm_Corless_coeff_P_succ
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_fbar_comp
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (N : ℕ) (w : ℕ → ZMod 2)
    (h : ∑ j ∈ range N, C (w j) * (fbar j * fbar (2 * N - 1 - j)) = 0) : ∀ j < N, w j = 0 := by
  -- substitute x = y + y²
  have hc := congrArg (fun p => p.comp (X + X ^ 2 : (ZMod 2)[X])) h
  simp only [zero_comp] at hc
  rw [Polynomial.sum_comp] at hc
  have hterm : ∀ j ∈ range N, (C (w j) * (fbar j * fbar (2 * N - 1 - j))).comp (X + X ^ 2)
      = C (w j) * (((1 + X) ^ (j + 1) + X ^ (j + 1))
        * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comp, C_comp, mul_comp, fbar_comp, fbar_comp,
      show 2 * N - 1 - j + 1 = 2 * N - j by omega]
  rw [Finset.sum_congr rfl hterm] at hc
  -- the constant coefficient: ∑ w j = 0
  have hsum : ∑ j ∈ range N, w j = 0 := by
    have := congrArg (fun p : (ZMod 2)[X] => p.coeff 0) hc
    simp only [finsetSum_coeff, coeff_C_mul, coeff_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j hj => by
      rw [coeff_P_zero N j (Finset.mem_range.mp hj), mul_one]
  -- the coefficient of y^(i+1) kills w i, by strong induction
  intro i hi
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have := congrArg (fun p : (ZMod 2)[X] => p.coeff (i + 1)) hc
    simp only [finsetSum_coeff, coeff_C_mul, coeff_zero] at this
    rw [Finset.sum_congr rfl fun j hj => by
      rw [coeff_P_succ N j i (Finset.mem_range.mp hj) hi]] at this
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_add] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j hj hji
      by_cases hle : j ≤ i
      · rw [ih j (by omega) (by omega), zero_mul]
      · simp [hle]
    · intro hi'
      exact absurd (Finset.mem_range.mpr hi) hi'
end Corless
