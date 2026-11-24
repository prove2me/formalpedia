-- Prove2me | solution 1 for BalanceSpecification.carrier_eq_of_language_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:44.569532+00:00
-- url     : https://prove2.me/submissions/6053d75b-3ecf-469a-a592-330f15f3e178

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_carrier_subset_of_language_subset

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {Y : ShiftSpace A}
    (h : language X = language Y) : X.carrier = Y.carrier := by
  apply Set.Subset.antisymm
  · exact carrier_subset_of_language_subset h.subset
  · exact carrier_subset_of_language_subset h.symm.subset
end BalanceSpecification
