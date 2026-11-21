-- Prove2me | solution 1 for Corless.det_CM_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:45.895983+00:00
-- url     : https://prove2.me/submissions/7135ac10-0092-481b-8bae-f6123d04a991

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Theorems.Thm_Corless_det_CM_one
public import Theorems.Thm_Corless_det_CM_succ_succ
public import Theorems.Thm_Corless_natDegree_E_le
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_succ_succ_left
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution : ∀ (m : ℕ) (s : ℕ → ℤ) (u : ℕ → ℂ),
    (∀ i, i + 1 < m → (s i : ℂ) = u i ^ 2) → (CM m u).det = reflect m (E s m)
  | 0, s, u, _ => by simp [E]
  | 1, s, u, _ => by
      rw [det_CM_one]
      simp [E]
  | m + 2, s, u, hsu => by
      rw [det_CM_succ_succ,
        solution (m + 1) (fun i => s (i + 1)) (fun i => u (i + 1)) (fun i hi => hsu _ (by omega)),
        solution m (fun i => s (i + 2)) (fun i => u (i + 2)) (fun i hi => hsu _ (by omega))]
      have hE : E s (m + 2) = E (fun i => s (i + 1)) (m + 1)
          + C (u 0 ^ 2) * X ^ 2 * E (fun i => s (i + 2)) m := by
        simp only [E]
        rw [Dv_succ_succ_left, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          Polynomial.map_C, Polynomial.map_X, map_add, map_mul, map_mul, expand_C, expand_X,
          ← hsu 0 (by omega)]
        simp
      rw [hE, reflect_add]
      -- the first term gains a factor X, the second loses X²
      have h1 : reflect (m + 2) (E (fun i => s (i + 1)) (m + 1))
          = X * reflect (m + 1) (E (fun i => s (i + 1)) (m + 1)) := by
        have := reflect_mul (1 : ℂ[X]) (E (fun i => s (i + 1)) (m + 1)) (F := 1) (G := m + 1)
          (by simp) (natDegree_E_le _ _)
        rw [one_mul, show 1 + (m + 1) = m + 2 by omega] at this
        rw [this, show (1 : ℂ[X]) = C 1 by simp, reflect_C]
        simp
      have h2 : reflect (m + 2) (C (u 0 ^ 2) * X ^ 2 * E (fun i => s (i + 2)) m)
          = C (u 0 ^ 2) * reflect m (E (fun i => s (i + 2)) m) := by
        have := reflect_mul (C (u 0 ^ 2) * X ^ 2) (E (fun i => s (i + 2)) m) (F := 2) (G := m)
          (by apply (natDegree_C_mul_le _ _).trans; simp) (natDegree_E_le _ _)
        rw [show 2 + m = m + 2 by omega] at this
        rw [this, reflect_C_mul_X_pow, revAt_le (le_refl 2), Nat.sub_self, pow_zero, mul_one]
      rw [h1, h2]
end Corless
