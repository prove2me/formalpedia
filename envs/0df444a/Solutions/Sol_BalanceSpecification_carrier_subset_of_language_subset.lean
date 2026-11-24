-- Prove2me | solution 1 for BalanceSpecification.carrier_subset_of_language_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:27.340861+00:00
-- url     : https://prove2.me/submissions/3e47eec9-a05a-4607-94bb-9b8a3943b79b

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_mem_carrier_iff_blocks

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {Y : ShiftSpace A}
    (h : language X ⊆ language Y) : X.carrier ⊆ Y.carrier := by
  intro x hx
  apply mem_carrier_iff_blocks.mpr
  intro k n
  exact h (block_mem_language hx k n)
end BalanceSpecification
