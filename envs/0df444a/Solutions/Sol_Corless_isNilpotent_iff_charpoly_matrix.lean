-- Prove2me | solution 1 for Corless.isNilpotent_iff_charpoly_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:37.502144+00:00
-- url     : https://prove2.me/submissions/b9a2e426-189c-4c2f-9e8b-364cb3215fbc

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
theorem _root_.solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    IsNilpotent A ↔ A.charpoly = X ^ m := by
  constructor
  · intro h
    simpa only [Fintype.card_fin, isNilpotent_iff_eq_zero, sub_eq_zero] using
      A.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  · intro h
    refine ⟨m, ?_⟩
    simpa only [h, map_pow, aeval_X] using A.aeval_self_charpoly
end Corless
