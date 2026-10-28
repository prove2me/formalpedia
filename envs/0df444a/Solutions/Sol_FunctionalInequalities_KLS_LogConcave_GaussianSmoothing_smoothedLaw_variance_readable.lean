-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_variance_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:38.437684+00:00
-- url     : https://prove2.me/submissions/27fee65b-822d-413d-b71e-60bfb1c4cf40

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_variance_readable

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
/-- Variances add under smoothing: `Var_{μ*γ_s}⟪v,·⟫ = Var_μ⟪v,·⟫ + ‖v‖²/(2s)`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
    variance (fun y : E => ⟪v, y⟫) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s) =
      variance (fun y : E => ⟪v, y⟫) μ + ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hX : MemLp (fun y : E => ⟪v, y⟫) 2 μ := by
    simpa only [id_eq, innerSL_apply_apply] using hμ2.continuousLinearMap_comp (innerSL ℝ v)
  have hY : MemLp (fun y : E => ⟪v, y⟫) 2 (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
    simpa only [id_eq, innerSL_apply_apply] using
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).continuousLinearMap_comp (innerSL ℝ v)
  have h := variance_add_prod hX hY
  rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_variance_readable hs] at h
  unfold FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw Measure.conv
  rw [variance_map (by fun_prop : AEMeasurable (fun y : E => ⟪v, y⟫) _)
    (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)]
  simpa only [Function.comp_def, inner_add_right] using h
