-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_one_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:52.707075+00:00
-- url     : https://prove2.me/submissions/7a34ace3-e3e9-4796-b950-d448c0daea7b

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov

noncomputable section
open Filter InnerProductSpace MeasureTheory Topology
open scoped RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
/-- The closed weighted gradient annihilates the constant one. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    hν.closedWeightedOperator m B hi
        ⟨FunctionalInequalities.L2.const ν 1, FunctionalInequalities.KLS.LogConcave.one_mem_domain_closedWeightedOperator m B hν hi⟩ = 0 := by
  let hac := hν.absolutelyContinuous_haar m hi
  let honeRaw : FunctionalInequalities.L2.const ν 1 ∈ (hν.weightedOperator m B hi).domain := by
    rw [FunctionalInequalities.Energy.WeightedGradient.L2_const_eq_toLp]
    exact FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν B hac (FunctionalInequalities.Energy.WeightedGradient.IsTest.const 1)
  let oneRaw : (hν.weightedOperator m B hi).domain := ⟨FunctionalInequalities.L2.const ν 1, honeRaw⟩
  have hraw : hν.weightedOperator m B hi oneRaw = 0 := by
    rw [FunctionalInequalities.Energy.WeightedGradient.operator_apply ν B hac (hν.frontier_support_eq_zero hi)
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.const 1) honeRaw (FunctionalInequalities.Energy.WeightedGradient.L2_const_eq_toLp ν 1)]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (FunctionalInequalities.Energy.WeightedGradient.IsTest.const
      (ν := ν) (B := B) 1).memLp_apply, Lp.coeFn_zero V 2 (ν : Measure V)] with x hx hzero
    rw [hx, hzero]
    exact congrFun (FunctionalInequalities.Energy.WeightedGradient.apply_const B 1) x
  have hclosure := (hν.weightedOperator m B hi).le_closure.2
    (x := oneRaw)
    (y := ⟨FunctionalInequalities.L2.const ν 1, FunctionalInequalities.KLS.LogConcave.one_mem_domain_closedWeightedOperator m B hν hi⟩) rfl
  rw [← hclosure, hraw]
