-- Prove2me | solution 1 for BalanceSpecification.codedShift_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:37.032577+00:00
-- url     : https://prove2.me/submissions/b75ebcae-4171-4927-8ca6-49c7bd4c22cf

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
public import Theorems.Thm_BalanceSpecification_isConcatenation_mono

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A] {C D : Set (Word A)} (hCD : C ⊆ D) :
    (codedShift C).carrier ⊆ (codedShift D).carrier :=
  closure_mono (fun _ hx => isConcatenation_mono hCD hx)
end BalanceSpecification
