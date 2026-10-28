-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_eq_zero_iff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:35.851987+00:00
-- url     : https://prove2.me/submissions/750b56ef-915f-4ee4-93c4-85046893cb28

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_one_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_eq_const_mean_of_closedWeightedOperator_eq_zero_readable

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
/-- **The kernel of the closed unit gradient is the constants**: `T̄ h = 0` exactly when `h` is the
`L²(ν)` constant equal to its mean. -/
theorem solution
    (h : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi h = 0 ↔
      (h : Lp ℝ 2 (ν : Measure V)) = FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (h : Lp ℝ 2 (ν : Measure V))) := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  constructor
  · intro h0
    exact FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero_readable m hν hi hνU
      hU.continuous h h0
  · intro hh
    let c := FunctionalInequalities.L2.mean ν (h : Lp ℝ 2 (ν : Measure V))
    let o : T.domain :=
      ⟨FunctionalInequalities.L2.const ν 1,
        FunctionalInequalities.KLS.LogConcave.one_mem_domain_closedWeightedOperator m
          (ContinuousLinearMap.id ℝ V) hν hi⟩
    have hh' : h = c • o := by
      apply Subtype.ext
      change (h : Lp ℝ 2 (ν : Measure V)) = c • (FunctionalInequalities.L2.const ν 1)
      calc
        (h : Lp ℝ 2 (ν : Measure V)) =
            FunctionalInequalities.L2.const ν c := hh
        _ = FunctionalInequalities.L2.const ν (c * 1) := by rw [mul_one]
        _ = c • FunctionalInequalities.L2.const ν 1 := FunctionalInequalities.L2.const_smul ν c 1
    have ho : T o = 0 := by
      change
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨FunctionalInequalities.L2.const ν 1,
              FunctionalInequalities.KLS.LogConcave.one_mem_domain_closedWeightedOperator m
                (ContinuousLinearMap.id ℝ V) hν hi⟩ = 0
      exact hν.closedWeightedOperator_one_eq_zero_readable m
        (ContinuousLinearMap.id ℝ V) hi
    have hres : T h = 0 := by
      have h' := congrArg (fun x : T.domain => T x) hh'
      calc
        T h = T (c • o) := h'
        _ = c • T o := T.toFun.map_smul c o
        _ = 0 := by rw [ho, smul_zero]
    simpa only [T] using hres
