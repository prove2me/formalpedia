-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.topologicallyMixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:55.303068+00:00
-- url     : https://prove2.me/submissions/d9daedda-a308-43e5-bfc4-f07309260361

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
public import Theorems.Thm_BalanceSpecification_topologicallyMixing_of_word_bridges
public import Theorems.Thm_BalanceSpecification_FiveSymbol_concat_twos_mem_language
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
open Set TopologicalSpace
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
open BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution : TopologicallyMixing shift := by
  apply topologicallyMixing_of_word_bridges
  intro u hu v hv
  refine ⟨u.length + 1, ?_⟩
  intro L hL
  have hfull := concat_twos_mem_language hu hv (show u.length < L by omega)
  exact ⟨List.replicate L 2,
    language_factorial shift (List.infix_append u (List.replicate L 2) v) hfull,
    List.length_replicate .., hfull⟩
end BalanceSpecification.FiveSymbol
