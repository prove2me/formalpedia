-- Prove2me | solution 1 for Corless.coeff_P_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:28.411112+00:00
-- url     : https://prove2.me/submissions/76987527-80f9-4b63-a6c8-07bf09b0be12

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (N j i : ℕ) (hj : j < N) (hi : i < N) :
    (((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))).coeff (i + 1)
      = ((2 * N + 1).choose (i + 1) : ZMod 2)
        + if j ≤ i then ((2 * N - j).choose (i - j) : ZMod 2) else 0 := by
  have h : ((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))
      = (1 + X) ^ (2 * N + 1) + X ^ (j + 1) * (1 + X) ^ (2 * N - j)
        + X ^ (2 * N - j) * (1 + X) ^ (j + 1) + X ^ (2 * N + 1) := by
    rw [show 2 * N + 1 = (j + 1) + (2 * N - j) by omega, pow_add, pow_add]
    ring
  rw [h]
  simp only [coeff_add, coeff_one_add_X_pow, coeff_X_pow_mul', coeff_X_pow]
  have h1 : ¬ (2 * N - j ≤ i + 1) := by omega
  have h2 : i ≠ 2 * N := by omega
  by_cases hji : j ≤ i
  · have h3 : j + 1 ≤ i + 1 := by omega
    simp [h1, h2, hji, h3, show i + 1 - (j + 1) = i - j by omega]
  · have h3 : ¬ (j + 1 ≤ i + 1) := by omega
    simp [h1, h2, hji, h3]
end Corless
