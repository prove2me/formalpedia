-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:37.989134+00:00
-- url     : https://prove2.me/submissions/09a80550-18b4-4943-853a-c0071c62f67f

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Comparison

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
end
end
end

section
noncomputable section
open MeasureTheory
open scoped ContDiff
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]
section
variable {μ : MeasureTheory.ProbabilityMeasure E}
/-- The `L²` realization agrees almost everywhere with the original test function. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.toL2_coeFn (f : Test μ) :
    f.toL2 =ᵐ[(μ : Measure E)] f.toFun :=
  f.memLp_two.coeFn_toLp
end
end
end
end

noncomputable section
open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)
/-- The concrete smooth-gradient family has exactly the smooth-test fixed-constant inequality.
Source: identical smooth finite-energy tests and `L2.variance_toLp`; no closure theorem is used. -/
theorem solution (C : NNReal) :
    FunctionalInequalities.Poincare.SmoothTest.Holds (μ : Measure E) (C : ℝ) ↔
      (FunctionalInequalities.Poincare.TestFamily.ofPreEnergy μ (FunctionalInequalities.Energy.SmoothGradient.preEnergy μ)).Holds C := by
  have hvariance (f : FunctionalInequalities.Energy.SmoothGradient.Test μ) :
      (FunctionalInequalities.L2.variance μ f.toL2 : ℝ) = ProbabilityTheory.variance f.toFun (μ : Measure E) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise μ f.toL2).trans
      (ProbabilityTheory.variance_congr f.toL2_coeFn)
  constructor
  · intro h
    change ∀ f : FunctionalInequalities.Energy.SmoothGradient.Test μ,
      FunctionalInequalities.L2.variance μ f.toL2 ≤ C * f.energy
    intro f
    apply NNReal.coe_le_coe.mp
    rw [hvariance, NNReal.coe_mul]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let t : FunctionalInequalities.Energy.SmoothGradient.Test μ :=
      ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    have ht := NNReal.coe_le_coe.mpr (h t)
    change (FunctionalInequalities.L2.variance μ t.toL2 : ℝ) ≤ (C * t.energy : NNReal) at ht
    rw [hvariance, NNReal.coe_mul] at ht
    exact ht
