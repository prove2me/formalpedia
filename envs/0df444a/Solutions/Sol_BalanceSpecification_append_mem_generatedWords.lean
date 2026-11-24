-- Prove2me | solution 1 for BalanceSpecification.append_mem_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:24.487655+00:00
-- url     : https://prove2.me/submissions/2ad26493-2ca8-4e51-9571-7d934ad85860

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {C : Set (Word A)} {u v : Word A}
    (hu : u ∈ generatedWords C) (hv : v ∈ generatedWords C) :
    u ++ v ∈ generatedWords C := by
  obtain ⟨us, hus, rfl⟩ := hu
  obtain ⟨vs, hvs, rfl⟩ := hv
  refine ⟨us ++ vs, ?_, List.flatten_append⟩
  intro w hw
  exact (List.mem_append.mp hw).elim (hus w) (hvs w)
end BalanceSpecification
