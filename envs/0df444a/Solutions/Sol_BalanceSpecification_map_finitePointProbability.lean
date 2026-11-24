-- Prove2me | solution 1 for BalanceSpecification.map_finitePointProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:53.023867+00:00
-- url     : https://prove2.me/submissions/b9c777b8-2511-4a32-942d-cc5400c6baed

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_finitePointProbability_apply


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [Fintype A] [DiscreteTopology A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution {I : Type*} [Fintype I] [Nonempty I]
    (x : I → X.carrier) {f : X.carrier → X.carrier} (hf : Measurable f) :
    (finitePointProbability x).map hf.aemeasurable = finitePointProbability (fun i => f (x i)) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext E hE
  change Measure.map f (finitePointProbability x : Measure X.carrier) E = _
  rw [Measure.map_apply hf hE, finitePointProbability_apply x (hf hE),
    finitePointProbability_apply (fun i => f (x i)) hE]
  rfl
end BalanceSpecification
