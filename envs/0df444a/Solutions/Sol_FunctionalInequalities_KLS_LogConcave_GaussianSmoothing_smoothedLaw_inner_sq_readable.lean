-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_inner_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:29.100887+00:00
-- url     : https://prove2.me/submissions/5dd731c9-dc23-4456-9898-2fab40830c64

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_mean_readable
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
/-- Raw directional second moments increase by `‖v‖²/(2s)`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) =
      (∫ y : E, ⟪v, y⟫ ^ 2 ∂μ) + ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_probability hs
  have hsm2 := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_two μ hμ2 hs
  have hX : MemLp (fun y : E => ⟪v, y⟫) 2 μ := by
    simpa only [id_eq, innerSL_apply_apply] using hμ2.continuousLinearMap_comp (innerSL ℝ v)
  have hY : MemLp (fun y : E => ⟪v, y⟫) 2 (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s) := by
    simpa only [id_eq, innerSL_apply_apply] using hsm2.continuousLinearMap_comp (innerSL ℝ v)
  have hm : (∫ y : E, ⟪v, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) = ∫ y : E, ⟪v, y⟫ ∂μ := by
    change (∫ y, (innerSL ℝ v) (id y) ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) = ∫ y, (innerSL ℝ v) (id y) ∂μ
    rw [(innerSL ℝ v).integral_comp_comm (hsm2.integrable one_le_two),
      (innerSL ℝ v).integral_comp_comm (hμ2.integrable one_le_two)]
    congr 1
    simpa only [id_eq] using FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean_readable μ hμ2 hs
  have hv := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_variance_readable μ hμ2 hs v
  rw [variance_eq_sub hY, variance_eq_sub hX, hm] at hv
  simp only [Pi.pow_apply] at hv
  linarith
