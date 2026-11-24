-- Prove2me | solution 1 for BalanceSpecification.translatedProbability_cylinder_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:06.042834+00:00
-- url     : https://prove2.me/submissions/bd3afe11-0948-49ee-8e95-494c1d5ee26c

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_cylinder_preimage_iterate
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
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
theorem _root_.solution (μ : ProbabilityMeasure X.carrier)
    (k : ℕ) (w : Word A) (l : ℤ) :
    (translatedProbability μ k : Measure X.carrier).real (cylinder X w l) =
      (μ : Measure X.carrier).real (cylinder X w ((k : ℤ) + l)) := by
  rw [measureReal_def]
  change (Measure.map ((shiftMap X)^[k]) (μ : Measure X.carrier) (cylinder X w l)).toReal = _
  rw [Measure.map_apply ((measurable_shiftMap X).iterate k) (measurableSet_cylinder X w l),
    cylinder_preimage_iterate]
  rfl
end BalanceSpecification
