-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.fderiv_logLaplace_fst_dir_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:38.145931+00:00
-- url     : https://prove2.me/submissions/5d56d598-3a8e-40d6-a4ad-6c338e465a7a

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_fderiv_logPartition_c_apply_readable

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open scoped ContDiff
section Bridges
variable {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup L]
  [NormedSpace ℝ L]
/-- The joint derivative in a first-factor direction is the partial derivative in the first factor. -/
theorem FunctionalInequalities.KLS.BKL.Localization.fderiv_fst_dir (H : E × L → ℝ) (p : E × L) (hH : DifferentiableAt ℝ H p) (u : E) :
    fderiv ℝ H p (u, 0) = fderiv ℝ (fun y => H (y, p.2)) p.1 u := by
  have h := hH.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  have h' : fderiv ℝ (fun y => H (y, p.2)) p.1 =
      (fderiv ℝ H p).comp (ContinuousLinearMap.inl ℝ E L) := h.fderiv
  rw [h']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
end Bridges
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
include hc in
/-- Joint smoothness of the log-Laplace transform `Λ(q) = ψ(q.1 + z, q.2) − ψ(q.1, q.2)`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.contDiff_logLaplace_joint (z : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞
      (fun q : Param n => logPartition μ (q.1 + z) q.2 - logPartition μ q.1 q.2) := by
  have hjoint := contDiff_logPartition_joint_readable μ hc
  have hmap : ContDiff ℝ ∞ (fun q : Param n => ((q.1 + z, q.2) : Param n)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  have h1 := hjoint.comp hmap
  have h1' : ContDiff ℝ ∞ (fun q : Param n => logPartition μ (q.1 + z) q.2) := by
    convert h1 using 1
    rfl
  exact h1'.sub hjoint
include hc in
/-- `D_c Λ[u] = ⟪u, a(c + z, Q) − a(c, Q)⟫` for the log-Laplace transform `Λ(q) = ψ(q.1 + z, q.2) − ψ(q.1, q.2)`. -/
theorem solution (z : EuclideanSpace ℝ (Fin n)) (p : FunctionalInequalities.KLS.BKL.Localization.Param n)
    (u : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Probability.Posterior.logPartition μ (q.1 + z) q.2 - FunctionalInequalities.Probability.Posterior.logPartition μ q.1 q.2) p (u, 0) =
      ⟪u, FunctionalInequalities.Probability.Posterior.posteriorMean μ (p.1 + z) p.2 - FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2⟫ := by
  have hjoint := FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_readable μ hc
  have hψ : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => FunctionalInequalities.Probability.Posterior.logPartition μ y p.2) := by
    have hmap : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => ((y, p.2) : FunctionalInequalities.KLS.BKL.Localization.Param n)) :=
      contDiff_id.prodMk contDiff_const
    have h := hjoint.comp hmap
    convert h using 1
    rfl
  have hψz : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => FunctionalInequalities.Probability.Posterior.logPartition μ (y + z) p.2) := by
    have hmap : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => y + z) :=
      contDiff_id.add contDiff_const
    have h := hψ.comp hmap
    convert h using 1
    rfl
  have hΛ := FunctionalInequalities.KLS.BKL.Localization.contDiff_logLaplace_joint μ hc z
  rw [FunctionalInequalities.KLS.BKL.Localization.fderiv_fst_dir _ p (hΛ.differentiable (by norm_num) p) u]
  change fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
    FunctionalInequalities.Probability.Posterior.logPartition μ (y + z) p.2 - FunctionalInequalities.Probability.Posterior.logPartition μ y p.2) p.1 u = _
  rw [fderiv_fun_sub (hψz.differentiable (by norm_num) p.1) (hψ.differentiable (by norm_num) p.1),
    sub_apply,
    fderiv_comp_add_right (f := fun y : EuclideanSpace ℝ (Fin n) => FunctionalInequalities.Probability.Posterior.logPartition μ y p.2) z,
    FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply_readable μ hc, FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply_readable μ hc, inner_sub_right]
