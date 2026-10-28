-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.row_joint_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:45.706242+00:00
-- url     : https://prove2.me/submissions/f42684d7-fa99-46a9-8ea4-63d58a668544

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticTilt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_Probability_covariance_quadraticTilt_tendsto_readable
import Theorems.Thm_FunctionalInequalities_Probability_integral_quadraticTilt_tendsto_readable

section
section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
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
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Set
section Laws
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- The quadratic tilts converge weakly to `μ` along any positive rate sequence `δ_j → 0`. -/
theorem FunctionalInequalities.Probability.quadraticTiltLaw_tendsto (μ : ProbabilityMeasure E) (δseq : ℕ → ℝ)
    (hδ : ∀ j, 0 < δseq j) (hlim : Tendsto δseq atTop (𝓝 0)) :
    Tendsto (fun j => quadraticTiltLaw μ (δseq j) (hδ j).le) atTop (𝓝 μ) := by
  have hwithin : Tendsto δseq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hδ⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hg : Integrable (fun x : E => g x) (μ : Measure E) :=
    (integrable_const ‖g‖).mono' g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall g.norm_coe_le_norm)
  exact (integral_quadraticTilt_tendsto_readable (μ : Measure E) (fun x => g x) hg).comp hwithin
/-- Means converge when `μ` has a first moment. -/
theorem FunctionalInequalities.Probability.integral_id_quadraticTilt_tendsto [CompleteSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : E => x) μ) :
    Tendsto (fun δ : ℝ => ∫ x : E, x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : E, x ∂μ)) :=
  integral_quadraticTilt_tendsto_readable μ (fun x => x) hint
/-- Second moments converge when `μ` has a second moment. -/
theorem FunctionalInequalities.Probability.integral_norm_sq_quadraticTilt_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ) :
    Tendsto (fun δ : ℝ => ∫ x : E, ‖x‖ ^ 2
      ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : E, ‖x‖ ^ 2 ∂μ)) :=
  integral_quadraticTilt_tendsto_readable μ (fun x => ‖x‖ ^ 2) hint
end Laws
end
end

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_tendsto_zero : Tendsto tiltRate atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
/-- For fixed `n`, the row converges (law and statistics) to the smoothing as `k → ∞`. -/
theorem solution (μ : ProbabilityMeasure E) (hμ2 : MemLp id 2 (μ : Measure E)) (n : ℕ) :
    Tendsto (fun k : ℕ => (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.rowLaw μ n k, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.statistics (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.rowLaw μ n k)))
      atTop (𝓝 (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianSeq μ n, FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.statistics (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianSeq μ n))) := by
  let ν : ProbabilityMeasure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianSeq μ n
  have hν2 : MemLp id 2 (ν : Measure E) :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_two (μ : Measure E) hμ2 (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have hr : Tendsto FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_tendsto_zero, Eventually.of_forall FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_pos⟩
  have hw := FunctionalInequalities.Probability.quadraticTiltLaw_tendsto ν FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_pos FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_tendsto_zero
  have hm := (FunctionalInequalities.Probability.integral_id_quadraticTilt_tendsto (ν : Measure E)
    (hν2.integrable one_le_two)).comp hr
  have hnorm : Integrable (fun y : E => ‖y‖ ^ 2) (ν : Measure E) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).1 hν2
  have hsecond := (FunctionalInequalities.Probability.integral_norm_sq_quadraticTilt_tendsto (ν : Measure E) hnorm).comp hr
  have hcov := (FunctionalInequalities.Probability.covariance_quadraticTilt_tendsto_readable ν hν2).comp hr
  exact hw.prodMk_nhds (hm.prodMk_nhds (hsecond.prodMk_nhds hcov))
