-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:23:08.217158+00:00
-- url     : https://prove2.me/submissions/1d8c8051-10f5-479e-923b-69a858f36577

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_eq_zero_iff_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_one_eq_zero_readable

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
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- In the heat model `ν = m.tilted (-U)`, a form-domain vector is orthogonal to the kernel of the
closed unit gradient exactly when its mean vanishes (the kernel is the constants). -/
theorem solution
    (y : Lp ℝ 2 (ν : Measure V)) :
    (∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
          ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) ↔ FunctionalInequalities.L2.mean ν y = 0 := by
    have inner_const_eq_mean_mul :
        ∀ (f : Lp ℝ 2 (ν : Measure V)) (c : ℝ),
          ⟪f, FunctionalInequalities.L2.const ν c⟫ = c * FunctionalInequalities.L2.mean ν f := by
      intro f c
      rw [MeasureTheory.L2.inner_def, FunctionalInequalities.L2.mean_eq_integral]
      calc
        (∫ x, ⟪f x, (FunctionalInequalities.L2.const ν c) x⟫_ℝ ∂(ν : Measure V)) =
            ∫ x, f x * c ∂(ν : Measure V) := by
              apply integral_congr_ae
              filter_upwards [FunctionalInequalities.L2.const_coeFn ν c] with x hx
              rw [hx]
              simp
              ring
        _ = (∫ x, f x ∂(ν : Measure V)) * c := by
              rw [integral_mul_const]
        _ = c * ∫ x, f x ∂(ν : Measure V) := by
              ring

    constructor
    · intro hy
      let k :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
        ⟨FunctionalInequalities.L2.const ν 1,
          FunctionalInequalities.KLS.LogConcave.one_mem_domain_closedWeightedOperator
            (ν := ν) m (ContinuousLinearMap.id ℝ V) hν hi⟩
      have hk :
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 := by
        simpa [k] using
          hν.closedWeightedOperator_one_eq_zero_readable
            m (ContinuousLinearMap.id ℝ V) hi
      have hinner : ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 :=
        hy k hk
      calc
        FunctionalInequalities.L2.mean ν y = 1 * FunctionalInequalities.L2.mean ν y := by ring
        _ = ⟪y, FunctionalInequalities.L2.const ν 1⟫ := by
          symm
          exact inner_const_eq_mean_mul y 1
        _ = ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ := by
          rfl
        _ = 0 := hinner
    · intro hy k hk
      have hkeq :
          (k : Lp ℝ 2 (ν : Measure V)) =
            FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) :=
        (FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_eq_zero_iff_readable
          m hν hi hνU hU k).mp hk
      calc
        ⟪y, (k : Lp ℝ 2 (ν : Measure V))⟫ =
            ⟪y, FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ := by
              exact congrArg (fun z => ⟪y, z⟫) hkeq
        _ = FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V)) * FunctionalInequalities.L2.mean ν y := by
              exact inner_const_eq_mean_mul y _
        _ = 0 := by
              rw [hy]
              simp
