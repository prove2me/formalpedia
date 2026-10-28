-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.inner_center_eq_zero_of_closedWeightedOperator_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:23:09.268259+00:00
-- url     : https://prove2.me/submissions/49d38674-2e2c-4587-9daa-018fc9adc4eb

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_eq_zero_iff_readable

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
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- Centered data are orthogonal to the kernel of the closed unit gradient. -/
theorem solution (u : Lp ℝ 2 (ν : Measure V))
    (k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (hk : hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0) :
    ⟪FunctionalInequalities.L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
  have hk' :
      (k : Lp ℝ 2 (ν : Measure V)) =
        FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) :=
    (FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_eq_zero_iff_readable m hν hi hνU hU k).1 hk
  have hinner :
      ⟪FunctionalInequalities.L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ =
        ⟪FunctionalInequalities.L2.center ν u,
          FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ :=
    congrArg (fun f : Lp ℝ 2 (ν : Measure V) =>
      ⟪FunctionalInequalities.L2.center ν u, f⟫) hk'
  calc
    ⟪FunctionalInequalities.L2.center ν u, (k : Lp ℝ 2 (ν : Measure V))⟫ =
        ⟪FunctionalInequalities.L2.center ν u,
          FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ := hinner
    _ = ⟪FunctionalInequalities.L2.center ν u,
          (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) • FunctionalInequalities.L2.const ν 1⟫ := by
      rw [← FunctionalInequalities.L2.const_smul, mul_one]
    _ = FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V)) *
          ⟪FunctionalInequalities.L2.center ν u, FunctionalInequalities.L2.const ν 1⟫ := by
      rw [inner_smul_right]
    _ = FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V)) *
          FunctionalInequalities.L2.mean ν (FunctionalInequalities.L2.center ν u) := by
      rfl
    _ = 0 := by
      rw [FunctionalInequalities.L2.mean_center, mul_zero]
