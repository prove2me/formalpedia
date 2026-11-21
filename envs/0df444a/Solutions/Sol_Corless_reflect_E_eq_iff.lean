-- Prove2me | solution 1 for Corless.reflect_E_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:39.696326+00:00
-- url     : https://prove2.me/submissions/6707a2a6-5962-4783-bd1f-cb7cbb800d54

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
theorem _root_.solution (s : ℕ → ℤ) (m : ℕ) : reflect m (E s m) = X ^ m ↔ Dv s m = 1 := by
  rw [← reflect_one (R := ℂ) m]
  constructor
  · intro h
    have hE : E s m = 1 := by
      simpa only [reflect_reflect] using congrArg (reflect m) h
    unfold E at hE
    have h1 : Polynomial.map (Int.castRingHom ℂ) (Dv s m) = 1 := by
      apply expand_injective (R := ℂ) (n := 2) (by norm_num)
      rw [hE, map_one]
    have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
      Polynomial.map_injective _ (RingHom.injective_int _)
    exact hinj (by rw [h1, Polynomial.map_one])
  · intro h
    simp [E, h]
end Corless
