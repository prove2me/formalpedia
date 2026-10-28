-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.sum_inner_inverseSqrt_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:33:58.868371+00:00
-- url     : https://prove2.me/submissions/b8d2c6dd-fa43-4597-b11f-4da36ec3c2f8

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open scoped ContDiff
section Trace
variable {n : ℕ}
/-- `Σ_k ⟪σ e_k, v⟫² = ⟪v, σ σ v⟫` for a self-adjoint `σ`. -/
theorem solution (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) (v : EuclideanSpace ℝ (Fin n)) :
    ∑ k, ⟪σ (EuclideanSpace.single k 1), v⟫ * ⟪σ (EuclideanSpace.single k 1), v⟫ =
      ⟪v, σ (σ v)⟫ := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have he : ∀ i, EuclideanSpace.single i (1 : ℝ) = e i := fun i =>
    (EuclideanSpace.basisFun_apply (Fin n) ℝ i).symm
  simp only [he]
  calc
    ∑ k, ⟪σ (e k), v⟫ * ⟪σ (e k), v⟫ = ∑ k, ⟪σ v, e k⟫ * ⟪e k, σ v⟫ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hσ, real_inner_comm (e k) (σ v)]
    _ = ⟪σ v, σ v⟫ := e.sum_inner_mul_inner (σ v) (σ v)
    _ = ⟪v, σ (σ v)⟫ := by rw [real_inner_comm, hσ]
