-- Prove2me | solution 1 for Corless.CM_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:58.325941+00:00
-- url     : https://prove2.me/submissions/652acd98-363a-4022-b5dc-791e99bf330a

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution (m : ℕ) (u : ℕ → ℂ) (i j : Fin m) :
    CM m u i j = if i = j then X else if (j : ℕ) = i + 1 then -C (u i)
      else if (i : ℕ) = j + 1 then C (u j) else 0 := by
  by_cases h : i = j
  · subst h
    simp [CM, T]
  · rw [CM, charmatrix_apply_ne _ _ _ h]
    simp only [T, h, ite_false]
    split_ifs <;> simp
end Corless
