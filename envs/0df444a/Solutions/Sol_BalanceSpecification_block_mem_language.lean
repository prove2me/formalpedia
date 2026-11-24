-- Prove2me | solution 1 for BalanceSpecification.block_mem_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:45.058229+00:00
-- url     : https://prove2.me/submissions/c82580b7-621c-43b1-9b15-8095765cc37d

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {x : Configuration A} (hx : x ∈ X.carrier)
    (k : ℤ) (n : ℕ) : block x k n ∈ language X := by
  exact ⟨x, hx, k, by rw [length_block]⟩
end BalanceSpecification
