-- Prove2me | solution 1 for DDMomentDRO.Type2.weak_duality_C18
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:59:38.610387+00:00
-- url     : https://prove2.me/submissions/0e519695-072a-4e90-9b1d-4d291e8eb4ac

import Mathlib
import Definitions.Def_DDMomentDRO_Type2_Setting

set_option autoImplicit false
open Matrix DDMomentDRO.Type2

theorem solution {I J K : ℕ}
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (x : Fin I → ℝ) (p : Fin K → ℝ) (hp : p ∈ amb2 ξ μ Sig x)
    (s : ℝ) (u : Fin J → ℝ) (Y : Matrix (Fin J) (Fin J) ℝ)
    (hdual : ∀ k, Qn x k ≤ s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace) :
    ∑ k, p k * Qn x k ≤ s + u ⬝ᵥ μ x + ((Sig x)ᵀ * Y).trace := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have step : ∑ k, p k * Qn x k ≤
      ∑ k, p k * (s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hdual k) (h4 k)
  refine step.trans (le_of_eq ?_)
  have e1 : ∑ k, p k * s = s := by rw [← Finset.sum_mul, h1, one_mul]
  have e2 : ∑ k, p k * (u ⬝ᵥ ξ k) = u ⬝ᵥ μ x := by
    rw [← h2, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
  have e3 : ∑ k, p k * ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace = ((Sig x)ᵀ * Y).trace := by
    rw [← h3, Matrix.transpose_sum, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, e1, e2, e3]
