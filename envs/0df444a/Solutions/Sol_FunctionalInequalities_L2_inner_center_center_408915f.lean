-- Prove2me | solution 1 for FunctionalInequalities.L2.inner_center_center_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:49:44.754509+00:00
-- url     : https://prove2.me/submissions/bb59c107-9825-4267-94fe-b484ab68a4a5

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities.L2 in
/-- Centering both arguments subtracts the product of their means from their inner product. -/
theorem solution (μ : ProbabilityMeasure α)
    (f g : Lp ℝ 2 (μ : Measure α)) :
    inner ℝ (FunctionalInequalities.L2.center μ f) (FunctionalInequalities.L2.center μ g) =
      inner ℝ f g - FunctionalInequalities.L2.mean μ f * FunctionalInequalities.L2.mean μ g := by
  have hf : FunctionalInequalities.L2.const μ (FunctionalInequalities.L2.mean μ f) = FunctionalInequalities.L2.mean μ f • FunctionalInequalities.L2.const μ 1 := by
    simpa using FunctionalInequalities.L2.const_smul μ (FunctionalInequalities.L2.mean μ f) 1
  have hg : FunctionalInequalities.L2.const μ (FunctionalInequalities.L2.mean μ g) = FunctionalInequalities.L2.mean μ g • FunctionalInequalities.L2.const μ 1 := by
    simpa using FunctionalInequalities.L2.const_smul μ (FunctionalInequalities.L2.mean μ g) 1
  rw [FunctionalInequalities.L2.center, FunctionalInequalities.L2.center, hf, hg]
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  have hfmean : inner ℝ f (FunctionalInequalities.L2.const μ 1) = FunctionalInequalities.L2.mean μ f := rfl
  have hgmean : inner ℝ (FunctionalInequalities.L2.const μ 1) g = FunctionalInequalities.L2.mean μ g := by rw [real_inner_comm]; rfl
  have hunit : inner ℝ (FunctionalInequalities.L2.const μ 1) (FunctionalInequalities.L2.const μ 1) = 1 := FunctionalInequalities.L2.mean_const μ 1
  rw [hfmean, hgmean, hunit]
  ring
