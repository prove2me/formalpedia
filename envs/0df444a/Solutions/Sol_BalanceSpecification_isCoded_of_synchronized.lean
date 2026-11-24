-- Prove2me | solution 1 for BalanceSpecification.isCoded_of_synchronized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:42.801057+00:00
-- url     : https://prove2.me/submissions/23f03c25-8cb6-4899-a356-3799ad2c5920

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SynchronizedCoded
public import Theorems.Thm_BalanceSpecification_codedShift_synchronizingCode

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hS : Synchronized X) : IsCoded X := by
  obtain ⟨v, hv⟩ := hS.2
  exact ⟨synchronizingCode X v, codedShift_synchronizingCode hS.1 hv⟩
end BalanceSpecification
