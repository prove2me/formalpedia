-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_center_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:40.924717+00:00
-- url     : https://prove2.me/submissions/93993de0-31cb-4fda-9643-e21849d8c027

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_one_eq_zero_readable

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
/-- Centering does not change the closed gradient: `T̄ (center u) = T̄ u`. -/
theorem solution
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
          FunctionalInequalities.KLS.LogConcave.center_mem_closedWeightedOperator_domain m hν hi u⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let c := FunctionalInequalities.L2.mean ν (u : Lp ℝ 2 (ν : Measure V))
  let o : T.domain :=
    ⟨FunctionalInequalities.L2.const ν 1,
      FunctionalInequalities.KLS.LogConcave.one_mem_domain_closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hν hi⟩

  have hu :
      (⟨FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
          FunctionalInequalities.KLS.LogConcave.center_mem_closedWeightedOperator_domain m hν hi u⟩ : T.domain) =
        u - c • o := by
    apply Subtype.ext
    change
      FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)) =
        (u : Lp ℝ 2 (ν : Measure V)) -
          c • (FunctionalInequalities.L2.const ν 1)
    simp only [FunctionalInequalities.L2.center]
    congr 1
    rw [← FunctionalInequalities.L2.const_smul, mul_one]

  have ho : T o = 0 := by
    change
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨FunctionalInequalities.L2.const ν 1,
            FunctionalInequalities.KLS.LogConcave.one_mem_domain_closedWeightedOperator m
              (ContinuousLinearMap.id ℝ V) hν hi⟩ = 0
    exact hν.closedWeightedOperator_one_eq_zero_readable m
      (ContinuousLinearMap.id ℝ V) hi

  have hmain :
      T
          ⟨FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
            FunctionalInequalities.KLS.LogConcave.center_mem_closedWeightedOperator_domain m hν hi u⟩ =
        T u := by
    have h := congrArg (fun x : T.domain => T x) hu
    calc
      T
          ⟨FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
            FunctionalInequalities.KLS.LogConcave.center_mem_closedWeightedOperator_domain m hν hi u⟩ =
          T (u - c • o) := h
      _ = T u - T (c • o) := by
        exact T.toFun.map_sub u (c • o)
      _ = T u - c • T o := by
        congr 1
        exact T.toFun.map_smul c o
      _ = T u := by
        rw [ho, smul_zero, sub_zero]

  exact hmain
