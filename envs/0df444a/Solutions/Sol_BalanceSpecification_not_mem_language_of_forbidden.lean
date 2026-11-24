-- Prove2me | solution 1 for BalanceSpecification.not_mem_language_of_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:36.149288+00:00
-- url     : https://prove2.me/submissions/c9f4bb59-52b5-4ddc-b930-7f00ba13be31

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
theorem _root_.solution {F : Set (Word A)} {w : Word A}
    (hw : w ∈ F) : w ∉ language (forbiddenShift F) := by
  rintro ⟨x, hx, k, hk⟩
  exact hx w hw k hk
end BalanceSpecification
