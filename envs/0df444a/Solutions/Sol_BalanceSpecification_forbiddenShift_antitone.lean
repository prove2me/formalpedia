-- Prove2me | solution 1 for BalanceSpecification.forbiddenShift_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:15.192302+00:00
-- url     : https://prove2.me/submissions/7772107c-0b6b-4422-b123-d7d18b43d54c

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {F G : Set (Word A)} (hFG : F ⊆ G) :
    (forbiddenShift G).carrier ⊆ (forbiddenShift F).carrier := by
  intro x hx w hw k
  exact hx w (hFG hw) k
end BalanceSpecification
