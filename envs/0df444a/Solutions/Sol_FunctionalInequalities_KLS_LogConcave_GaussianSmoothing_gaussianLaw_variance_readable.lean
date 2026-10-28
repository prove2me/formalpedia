-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_variance_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:51.36105+00:00
-- url     : https://prove2.me/submissions/f5744a99-a366-4ed0-9225-a2180ea4a72e

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_inner_sq_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_mean_zero_readable

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
/-- `Var_{γ_s}⟪v,·⟫ = ‖v‖²/(2s)`. -/
theorem solution {s : ℝ} (hs : 0 < s) (v : E) :
    variance (fun y : E => ⟪v, y⟫) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) = ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have h2 : MemLp (fun y : E => ⟪v, y⟫) 2 (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
    simpa only [id_eq, innerSL_apply_apply] using
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).continuousLinearMap_comp (innerSL ℝ v)
  have h0 : (∫ y : E, ⟪v, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = 0 := by
    change (∫ y, (innerSL ℝ v) (id y) ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = 0
    rw [(innerSL ℝ v).integral_comp_comm ((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).integrable one_le_two)]
    simp only [id_eq]
    rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_mean_zero_readable hs]
    simp
  rw [variance_eq_sub h2, h0]
  simp only [Pi.pow_apply]
  rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq_readable hs]
  simp
