-- Prove2me | solution 1 for Corless.natDegree_Dv_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:35.159096+00:00
-- url     : https://prove2.me/submissions/fc826c53-9e28-44df-ba46-032274884a30

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_succ_succ
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution (s : ℕ → ℤ) : ∀ j, (Dv s j).natDegree ≤ j / 2
  | 0 => by simp
  | 1 => by simp
  | j + 2 => by
      rw [Dv_succ_succ]
      have h1 := solution s (j + 1)
      have h0 := solution s j
      apply (natDegree_add_le _ _).trans
      apply max_le
      · exact h1.trans (by omega)
      · apply (natDegree_mul_le).trans
        have : (C (s j : ℤ) * X : ℤ[X]).natDegree ≤ 1 := by
          apply (natDegree_C_mul_le _ _).trans; simp
        omega
end Corless
