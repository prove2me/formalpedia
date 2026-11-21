-- Prove2me | solution 1 for Corless.T_nilpotent_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:50:10.2008+00:00
-- url     : https://prove2.me/submissions/47153de2-a4e6-4b8c-8c0d-7ee842107749

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Theorems.Thm_Corless_charmatrix_T
public import Theorems.Thm_Corless_det_CM_eq
public import Theorems.Thm_Corless_isNilpotent_iff_charpoly_matrix
public import Theorems.Thm_Corless_reflect_E_eq_iff
public import Theorems.Thm_Corless_entrySign_one
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_corless
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero


attribute [local simp] Corless.entrySign_one
attribute [local simp] Corless.entrySign_I

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution {u : ℕ → ℂ} {m : ℕ}
    (hu : ∀ i, i + 1 < m → u i = 1 ∨ u i = Complex.I) (hm : 1 ≤ m) :
    IsNilpotent (T m u) ↔
      ∃ k, m = 2 ^ (k + 1) - 1 ∧ Fam k (fun i => entrySign (u i)) := by
  set s : ℕ → ℤ := fun i => entrySign (u i) with hs
  have hsu : ∀ i, i + 1 < m → (s i : ℂ) = u i ^ 2 := by
    intro i hi
    rcases hu i hi with h | h <;> simp [hs, h]
  have hsign : IsSign s m := by
    intro i _
    by_cases h : u i = 1 <;> simp [hs, entrySign, h]
  rw [isNilpotent_iff_charpoly_matrix, Matrix.charpoly, charmatrix_T, det_CM_eq m s u hsu,
    reflect_E_eq_iff, corless hsign hm]
end Corless
