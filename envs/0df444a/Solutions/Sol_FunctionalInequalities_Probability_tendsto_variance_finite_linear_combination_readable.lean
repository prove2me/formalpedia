-- Prove2me | solution 1 for FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:55.505501+00:00
-- url     : https://prove2.me/submissions/64c0611c-ec95-4bb5-94d2-491b96d78f13

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance

noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
/-- The mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_mean (μ : ProbabilityMeasure α) : Continuous (mean μ) :=
  continuous_id.inner continuous_const
/-- Subtracting the mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_center (μ : ProbabilityMeasure α) : Continuous (center μ) := by
  apply (continuous_id.sub ((continuous_mean μ).smul continuous_const) :
    Continuous (fun f : Lp ℝ 2 (μ : Measure α) ↦ f - mean μ f • const μ 1)).congr
  intro f
  simp only [center, ← const_smul, mul_one]
  rfl
/-- Variance is continuous in `L²`, including at constant functions. -/
theorem FunctionalInequalities.L2.continuous_variance (μ : ProbabilityMeasure α) : Continuous (variance μ) :=
  (continuous_center μ).nnnorm.pow 2
/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem FunctionalInequalities.L2.coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl
/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem FunctionalInequalities.L2.coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]
end
noncomputable section
open MeasureTheory Filter
open scoped Topology
theorem solution
    {alpha I : Type*} [MeasurableSpace alpha] [Fintype I]
    (mu : ProbabilityMeasure alpha) (f : I → alpha → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (mu : Measure alpha))
    (c : ℕ → I → ℝ) (b : I → ℝ)
    (hc : ∀ i, Tendsto (fun k => c k i) atTop (𝓝 (b i))) :
    Tendsto (fun k => ProbabilityTheory.variance (fun x => ∑ i, c k i * f i x) (mu : Measure alpha))
      atTop (𝓝 (ProbabilityTheory.variance (fun x => ∑ i, b i * f i x) (mu : Measure alpha))) := by
  classical
  let F (a : I → ℝ) : Lp ℝ 2 (mu : Measure alpha) := ∑ i, a i • (hf i).toLp (f i)
  have hrep (a : I → ℝ) : (F a : alpha → ℝ) =ᵐ[(mu : Measure alpha)]
      fun x => ∑ i, a i * f i x := by
    have hi (i : I) : (a i • (hf i).toLp (f i) : Lp ℝ 2 (mu : Measure alpha)) =ᵐ[(mu : Measure alpha)]
        fun x => a i * f i x := by
      filter_upwards [Lp.coeFn_smul (a i) ((hf i).toLp (f i)), (hf i).coeFn_toLp] with x h1 h2
      simpa only [Pi.smul_apply, smul_eq_mul, h2] using h1
    apply (Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • (hf i).toLp (f i))).trans
    filter_upwards [ae_all_iff.mpr hi] with x hx
    exact Finset.sum_congr rfl fun i _ => hx i
  have hF : Tendsto (fun k => F (c k)) atTop (𝓝 (F b)) := by
    apply tendsto_finsetSum
    intro i _
    exact (hc i).smul tendsto_const_nhds
  have hv (a : I → ℝ) : (FunctionalInequalities.L2.variance mu (F a) : ℝ) =
      ProbabilityTheory.variance (fun x => ∑ i, a i * f i x) (mu : Measure alpha) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise mu (F a)).trans
      (ProbabilityTheory.variance_congr (hrep a))
  have h := (NNReal.continuous_coe.comp (FunctionalInequalities.L2.continuous_variance mu)).continuousAt.tendsto.comp hF
  change Tendsto (fun k => (FunctionalInequalities.L2.variance mu (F (c k)) : ℝ)) atTop
    (𝓝 (FunctionalInequalities.L2.variance mu (F b) : ℝ)) at h
  simpa only [hv] using h
