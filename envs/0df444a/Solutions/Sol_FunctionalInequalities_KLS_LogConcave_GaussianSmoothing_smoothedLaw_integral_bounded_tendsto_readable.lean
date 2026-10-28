-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_integral_bounded_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:57.877247+00:00
-- url     : https://prove2.me/submissions/bf209acd-f6e4-4994-821d-8047bca177a6

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_normalizedDensity_tendsto_L1_readable

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.lintegral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x : V, ENNReal.ofReal (normalizedDensity ρ s x) = 1 := by
  have hprob := smoothedLaw_probability (ν := ν) hs
  rw [isProbabilityMeasure_iff] at hprob
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs,
    withDensity_apply _ MeasurableSet.univ] at hprob
  simpa only [Measure.restrict_univ] using hprob
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    Integrable (normalizedDensity ρ s) (volume : Measure V) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)).mp
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp
end
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Bornology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
section WeakConvergence
open Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.source_density_integrable {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) : Integrable ρ volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable hρ.measurable.aestronglyMeasurable
    (ae_of_all _ fun y => hρ.nonneg y)).mp
  have h : μ Set.univ = 1 := measure_univ
  rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
  have hi : (∫⁻ y : E, ENNReal.ofReal (ρ y)) = 1 := by simpa only [Measure.restrict_univ] using h
  rw [hi]
  simp
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density_integral (g : E → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (f : BoundedContinuousFunction E ℝ) : (∫ y, f y ∂(volume.withDensity (fun y => ENNReal.ofReal (g y)))) =
      ∫ y : E, g y * f y := by
  rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (hg0 y), smul_eq_mul]
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bounded_density_integrable {g : E → ℝ} (hg : Integrable g volume)
    (f : BoundedContinuousFunction E ℝ) : Integrable (fun y => g y * f y) volume := by
  refine (hg.norm.mul_const ‖f‖).mono'
    (hg.aestronglyMeasurable.mul f.continuous.measurable.aestronglyMeasurable) ?_
  filter_upwards [] with y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)
/-- Integrals of bounded continuous functions against the smoothed laws converge to those against `μ`
(`L¹` convergence of the normalized densities). -/
theorem solution {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ) (f : BoundedContinuousFunction E ℝ) :
    Tendsto (fun s : ℝ => ∫ y, f y ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) atTop (𝓝 (∫ y, f y ∂μ)) := by
  have hρi := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.source_density_integrable hρ
  have hlim : Tendsto (fun s : ℝ => ‖f‖ * ∫ y : E, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y|)
      atTop (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1_readable hρ).const_mul ‖f‖
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  have hFi := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity hρ hs
  have hFd := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bounded_density_integrable hFi f
  have hρd := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bounded_density_integrable hρi f
  have hdiff := hFi.sub hρi
  have hD := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bounded_density_integrable hdiff f
  have hEq : (∫ y, f y ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) - (∫ y, f y ∂μ) =
      ∫ y : E, (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y := by
    rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_eq_withDensity_normalizedDensity hρ hs, ← hρ.withDensity_eq,
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density_integral _ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_measurable hρ.measurable hs)
        (fun y => (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_pos hρ hs y).le), FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density_integral _ hρ.measurable hρ.nonneg,
      ← integral_sub hFd hρd]
    congr 1
    funext y
    ring
  rw [hEq]
  calc
    ‖∫ y : E, (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y‖ ≤
        ∫ y : E, ‖(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : E, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y| * ‖f‖ := by
      apply integral_mono hD.norm (hdiff.abs.mul_const ‖f‖)
      intro y
      change ‖(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y) * f y‖ ≤ |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y| * ‖f‖
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (abs_nonneg _)
    _ = ‖f‖ * ∫ y : E, |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s y - ρ y| := by rw [integral_mul_const]; ring
