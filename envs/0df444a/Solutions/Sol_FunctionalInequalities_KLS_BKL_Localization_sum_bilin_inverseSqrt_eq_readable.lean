-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.sum_bilin_inverseSqrt_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:23.031692+00:00
-- url     : https://prove2.me/submissions/2d73777c-36f5-4d50-91bc-936ac3f30116

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open scoped ContDiff
section Trace
variable {n : ℕ}
/-- Trace rearrangement `Σ_k B(σ e_k, σ e_k) = Σ_i B(σ σ e_i, e_i)` for a self-adjoint `σ`. -/
theorem solution (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ)
    (σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hσ : ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫) :
    ∑ k, B (σ (EuclideanSpace.single k 1)) (σ (EuclideanSpace.single k 1)) =
      ∑ i, B (σ (σ (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have he : ∀ i, EuclideanSpace.single i (1 : ℝ) = e i := fun i =>
    (EuclideanSpace.basisFun_apply (Fin n) ℝ i).symm
  simp only [he]
  have hσe : ∀ i, σ (e i) = ∑ k, ⟪e i, σ (e k)⟫ • e k := by
    intro i
    conv_lhs => rw [← e.sum_repr' (σ (e i))]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [← hσ (e i) (e k), real_inner_comm]
  calc
    ∑ k, B (σ (e k)) (σ (e k)) = ∑ k, B (σ (e k)) (∑ i, ⟪e i, σ (e k)⟫ • e i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [e.sum_repr' (σ (e k))]
    _ = ∑ k, ∑ i, ⟪e i, σ (e k)⟫ * B (σ (e k)) (e i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul]
    _ = ∑ i, ∑ k, ⟪e i, σ (e k)⟫ * B (σ (e k)) (e i) := Finset.sum_comm
    _ = ∑ i, B (σ (∑ k, ⟪e i, σ (e k)⟫ • e k)) (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum, map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    _ = ∑ i, B (σ (σ (e i))) (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hσe i]
