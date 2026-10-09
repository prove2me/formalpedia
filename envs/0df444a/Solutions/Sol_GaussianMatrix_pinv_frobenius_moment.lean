-- Prove2me | solution 1 for GaussianMatrix.pinv_frobenius_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:59:54.893462+00:00
-- url     : https://prove2.me/submissions/b8599bbc-591f-438f-9c2c-ff3b57612075

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_inverse_wishart_mean

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Deterministic identity: `‖G†‖_F² = tr((G Gᵀ)⁻¹)` for every real matrix `G`
(both sides vanish when `G Gᵀ` is singular, by Mathlib's convention `A⁻¹ = 0`). -/
theorem frobSq_pinvR_eq_trace_inv {r k : ℕ} (G : Matrix (Fin r) (Fin k) ℝ) :
    frobSq (pinvR G) = ∑ i, (G * Gᵀ)⁻¹ i i := by
  set A : Matrix (Fin r) (Fin r) ℝ := G * Gᵀ with hA
  set M : Matrix (Fin r) (Fin r) ℝ := A⁻¹ with hM
  have hAt : Aᵀ = A := by rw [hA, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hMt : Mᵀ = M := by rw [hM, Matrix.transpose_nonsing_inv, hAt]
  have hkey : (pinvR G)ᵀ * pinvR G = M := by
    unfold pinvR
    rw [← hA, ← hM, Matrix.transpose_mul, Matrix.transpose_transpose, hMt]
    by_cases h : IsUnit A.det
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc G, ← hA, hM, Matrix.mul_nonsing_inv A h,
        Matrix.mul_one]
    · have h0 : M = 0 := by rw [hM]; exact Matrix.nonsing_inv_apply_not_isUnit A h
      rw [h0]; simp
  have htr : frobSq (pinvR G) = Matrix.trace ((pinvR G)ᵀ * pinvR G) := by
    unfold frobSq Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [sq]
  rw [htr, hkey]
  rfl

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 2 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G))) (gaussianMatrix r k) ∧
    ∫ G, frobSq (pinvR (Matrix.of G)) ∂(gaussianMatrix r k) = (r : ℝ) / ((k : ℝ) - r - 1) := by
  obtain ⟨hint, hval⟩ := GaussianMatrix.inverse_wishart_mean hrk
  have hfun : (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)))
      = fun G => ∑ i, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i := by
    funext G; exact frobSq_pinvR_eq_trace_inv _
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => hint i i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hint i i]
  simp only [hval, Matrix.one_apply_eq, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring
