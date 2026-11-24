-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.none_not_mem_map_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:53.695605+00:00
-- url     : https://prove2.me/submissions/65ca463f-3bfa-4f9f-800f-ad700009e2f6

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (v : Word A) : (none : Option A) ∉ v.map some := by
  intro h
  obtain ⟨a, _, ha⟩ := List.mem_map.mp h
  exact Option.some_ne_none a ha
end BalanceSpecification.MarkerExtension
