-- Prove2me | solution 1 for BalanceSpecification.language_avoids_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:11.309199+00:00
-- url     : https://prove2.me/submissions/c91ea3fc-9ab4-41aa-93c4-a8b65e279461

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Theorems.Thm_BalanceSpecification_not_mem_language_of_forbidden
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {F : Set (Word A)} {u : Word A}
    (hu : u ∈ language (forbiddenShift F)) : ∀ w ∈ F, ¬ w <:+: u := by
  intro w hw hwu
  exact not_mem_language_of_forbidden hw ((language_factorial (forbiddenShift F)) hwu hu)
end BalanceSpecification
