-- Prove2me | solution 1 for BalanceSpecification.continuous_shiftMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:54.061543+00:00
-- url     : https://prove2.me/submissions/6add3324-60a6-4681-9f70-50494dfc7ea1

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) : Continuous (shiftMap X) := by
  exact ((SymbolicDynamics.FullShift.continuous_shift 1).comp continuous_subtype_val).subtype_mk _
end BalanceSpecification
