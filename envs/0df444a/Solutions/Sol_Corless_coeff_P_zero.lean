-- Prove2me | solution 1 for Corless.coeff_P_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:27.943496+00:00
-- url     : https://prove2.me/submissions/8d549374-6384-48a5-a745-5b86cfc68412

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
theorem _root_.solution (N j : ℕ) (hj : j < N) :
    (((1 + X : (ZMod 2)[X]) ^ (j + 1) + X ^ (j + 1))
      * ((1 + X) ^ (2 * N - j) + X ^ (2 * N - j))).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_mul]
  have hright : 2 * N - j ≠ 0 := by omega
  simp [hright]
end Corless
