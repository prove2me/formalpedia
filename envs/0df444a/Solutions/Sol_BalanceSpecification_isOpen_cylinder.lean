-- Prove2me | solution 1 for BalanceSpecification.isOpen_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:04.953042+00:00
-- url     : https://prove2.me/submissions/70c6f61d-7af9-4011-be5c-e1ca19e045e6

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
theorem _root_.solution [DiscreteTopology A] (X : ShiftSpace A) (w : Word A) (k : ℤ) :
    IsOpen (cylinder X w k) :=
  (isOpen_wordCylinder w k).preimage continuous_subtype_val
end BalanceSpecification
