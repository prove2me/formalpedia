-- Prove2me | solution 1 for BalanceSpecification.translatedProbability_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:16.191788+00:00
-- url     : https://prove2.me/submissions/d6d69c45-c31d-45bf-9df4-8dc51d74327f

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_measurable_shiftMap


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (μ : ProbabilityMeasure X.carrier) (a b : ℕ) :
    translatedProbability (translatedProbability μ a) b = translatedProbability μ (a + b) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map ((shiftMap X)^[b]) (Measure.map ((shiftMap X)^[a]) (μ : Measure X.carrier)) =
    Measure.map ((shiftMap X)^[a + b]) (μ : Measure X.carrier)
  rw [Measure.map_map ((measurable_shiftMap X).iterate b) ((measurable_shiftMap X).iterate a)]
  congr 1
  rw [← Function.iterate_add, Nat.add_comm]
end BalanceSpecification
