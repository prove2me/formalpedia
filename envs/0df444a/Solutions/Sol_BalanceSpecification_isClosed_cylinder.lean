-- Prove2me | solution 1 for BalanceSpecification.isClosed_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:48.338896+00:00
-- url     : https://prove2.me/submissions/ea599fe1-51a3-4244-bc8e-49fa676a94a3

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_isClosed_wordCylinder


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution [DiscreteTopology A] (X : ShiftSpace A) (w : Word A) (k : ℤ) :
    IsClosed (cylinder X w k) :=
  (isClosed_wordCylinder w k).preimage continuous_subtype_val
end BalanceSpecification
