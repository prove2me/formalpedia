-- Prove2me | solution 1 for BalanceSpecification.bsm_iff_hasVariableSpecification_of_entropy_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:20.485802+00:00
-- url     : https://prove2.me/submissions/3cff7e9b-5fb9-4288-90ae-8c0a87681f11

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_bsm_iff_finite_carrier_of_entropy_zero
public import Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_finite_irreducible
public import Theorems.Thm_BalanceSpecification_biBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) (hirr : Irreducible X) :
    BoundedlySupermultiplicative (language X) ↔ HasVariableSpecification X := by
  constructor
  · intro hbsm
    exact hasVariableSpecification_of_finite_irreducible
      ((bsm_iff_finite_carrier_of_entropy_zero hX hh).mp hbsm) hX hirr
  · intro hspec
    exact boundedlySupermultiplicative_of_rightBalanced (language_factorial X)
      (biBalanced_of_hasVariableSpecification hX hspec).1
end BalanceSpecification
