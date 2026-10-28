-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covarianceBilin_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:26.828805+00:00
-- url     : https://prove2.me/submissions/0f0535ec-ace2-45e3-95ea-6e30bcdb1698

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_variance_readable

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- `γ_s` has a finite second moment. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two {s : ℝ} (hs : 0 < s) : MemLp id 2 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_readable (E := E) hs
  exact (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    (Probability.integrable_norm_pow_of_integrable_exp_norm (by norm_num : (0 : ℝ) < 1) he 2)
omit [CompleteSpace E] in
/-- The smoothed law `μ * γ_s` has a finite second moment when `μ` does. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_two (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) : MemLp id 2 (smoothedLaw μ s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  unfold smoothedLaw Measure.conv
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)).2
  exact (hμ2.comp_fst (gaussianLaw s)).add ((gaussianLaw_memLp_two hs).comp_snd μ)
/-- The covariance form of the smoothed law is `Cov_μ + ⟪·,·⟫/(2s)`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v w : E) :
    covarianceBilin (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s) v w = covarianceBilin μ v w + ⟪v, w⟫ / (2 * s) := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_probability hs
  have hsm2 := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_two μ hμ2 hs
  have hdiag (u : E) : covarianceBilin (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s) u u =
      covarianceBilin μ u u + ‖u‖ ^ 2 / (2 * s) := by
    rw [covarianceBilin_self hsm2, covarianceBilin_self hμ2]
    exact FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_variance_readable μ hμ2 hs u
  have hv := hdiag v
  have hw := hdiag w
  have hsum := hdiag (v + w)
  simp only [map_add, add_apply] at hsum
  rw [covarianceBilin_comm (μ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s) w v, covarianceBilin_comm (μ := μ) w v,
    norm_add_sq_real] at hsum
  field_simp [hs.ne'] at hv hw hsum ⊢
  nlinarith
