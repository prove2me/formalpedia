-- Prove2me | solution 1 for Corless.Dv_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:32.465407+00:00
-- url     : https://prove2.me/submissions/1f1ea1b5-1e00-494e-a672-dec1e55dbe99

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_succ_succ
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (s : ℕ → ℤ) : ∀ j, (Dv s j).coeff 0 = 1
  | 0 => by simp
  | 1 => by simp
  | j + 2 => by
      rw [Dv_succ_succ, coeff_add, solution s (j + 1), mul_assoc, coeff_C_mul,
        coeff_X_mul_zero]
      simp
end Corless
