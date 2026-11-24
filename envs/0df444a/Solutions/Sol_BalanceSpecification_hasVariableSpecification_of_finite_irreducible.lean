-- Prove2me | solution 1 for BalanceSpecification.hasVariableSpecification_of_finite_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:27.942804+00:00
-- url     : https://prove2.me/submissions/e4768e17-e8c1-4b10-b457-82f6ac3f0dce

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_finite_irreducible_single_orbit
public import Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_single_periodic_orbit

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (hfin : X.carrier.Finite)
    (hX : X.carrier.Nonempty) (hirr : Irreducible X) : HasVariableSpecification X := by
  obtain ⟨x, hx, ⟨p, hp, hperiod⟩, horbit⟩ := finite_irreducible_single_orbit hfin hX hirr
  exact hasVariableSpecification_of_single_periodic_orbit hx hp hperiod horbit
end BalanceSpecification
