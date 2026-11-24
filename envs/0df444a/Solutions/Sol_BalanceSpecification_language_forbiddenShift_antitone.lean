-- Prove2me | solution 1 for BalanceSpecification.language_forbiddenShift_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:45.557769+00:00
-- url     : https://prove2.me/submissions/54d38bf3-3394-4f41-89b6-0f16120d53a0

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Theorems.Thm_BalanceSpecification_forbiddenShift_antitone

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {F G : Set (Word A)} (hFG : F ⊆ G) :
    language (forbiddenShift G) ⊆ language (forbiddenShift F) := by
  rintro w ⟨x, hx, k, hk⟩
  exact ⟨x, forbiddenShift_antitone hFG hx, k, hk⟩
end BalanceSpecification
