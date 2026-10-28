-- Prove2me | solution 1 for FunctionalInequalities.Energy.LipschitzGradient.holds_ofPreEnergy_of_localSlope_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:29.251986+00:00
-- url     : https://prove2.me/submissions/1dbec419-0af0-4428-8a72-813354f820c9

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_admissible_iff_memLp_gradient_readable
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_readable

section
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
/-- The `NNReal` variance of a pointwise square-integrable function is Mathlib's real variance
converted to `NNReal`; no information is lost because pointwise variance is nonnegative. -/
theorem FunctionalInequalities.L2.variance_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    variance μ (hf.toLp f) =
      (ProbabilityTheory.variance f (μ : Measure α)).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg f (μ : Measure α))]
  exact (coe_variance_eq_pointwise μ (hf.toLp f)).trans
    (ProbabilityTheory.variance_congr hf.coeFn_toLp)
end
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end

section
noncomputable section
open MeasureTheory Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : MeasureTheory.ProbabilityMeasure E) (m : MeasureTheory.Measure E)
  [MeasureTheory.Measure.IsAddHaarMeasure m]
omit sct in
/-- Step 2: Rademacher and absolute continuity identify the two pointwise energies almost
everywhere for locally Lipschitz tests, with no integrability or density lower bound premise. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_ae_eq_norm_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (fun x ↦ apply f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖) := by
  filter_upwards [hν.ae_le
    (Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hf m)]
    with x hx
  exact apply_eq_norm_gradient_readable f x hx
omit sct in
/-- Step 3: equality of the extended local-slope and gradient energies, also when infinite.
The lintegral keeps nonintegrable functions from acquiring a spurious zero energy. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    energy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E) := by
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [apply_ae_eq_norm_gradient ν m hν f hf] with x hx
  rw [hx]
section RealIntegral
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
/-- The literature energy of a locally Lipschitz function with square-integrable gradient is the
real integral of the squared gradient norm, under absolute continuity. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_integral_gradient
    (hac : (ν : Measure V) ≪ m) (f : V → ℝ) (hf : LocallyLipschitz f)
    (hg : MemLp (gradient f) 2 (ν : Measure V)) :
    energy ν f = ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V)) := by
  rw [energy_eq_lintegral_gradient ν m hac f hf,
    ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm hg.1).mp hg)
      (ae_of_all _ fun x ↦ sq_nonneg ‖gradient f x‖)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
end RealIntegral
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
section Bridge
/-- A literature constant is valid on the raw globally Lipschitz gradient tests. -/
theorem solution (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
    (h : FunctionalInequalities.Poincare.LocalSlope.Holds ν C) :
    (FunctionalInequalities.Poincare.TestFamily.ofPreEnergy ν
      (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac))).Holds C := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (FunctionalInequalities.Energy.WeightedGradient.mem_domain_operator_iff ν _ hac x).mp hx
  have hT := FunctionalInequalities.Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr hg hx rfl
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [FunctionalInequalities.Energy.WeightedGradient.apply_id] using hg.memLp_apply
  obtain ⟨K, hK⟩ := hg.1
  have hlit := h g ((FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_readable ν m hac g).mpr
    ⟨hK.locallyLipschitz, hg.memLp, hgrad⟩)
  rw [← ProbabilityTheory.ofReal_variance hg.memLp,
    FunctionalInequalities.Energy.LocalSlope.energy_eq_integral_gradient ν m hac g hK.locallyLipschitz hgrad,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg] at hlit
  have hreal : ProbabilityTheory.variance g (ν : Measure V) ≤
      (C : ℝ) * ∫ x, ‖gradient g x‖ ^ 2 ∂(ν : Measure V) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.2 (integral_nonneg fun x ↦ sq_nonneg _))).mp hlit
  change FunctionalInequalities.L2.variance ν (hg.memLp.toLp g) ≤
    C * ‖FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac ⟨_, hx⟩‖₊ ^ 2
  rw [hT, FunctionalInequalities.L2.variance_toLp, ← NNReal.coe_le_coe]
  push_cast
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _), FunctionalInequalities.L2.norm_toLp_sq,
    FunctionalInequalities.Energy.WeightedGradient.apply_id]
  exact hreal
