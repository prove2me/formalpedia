-- Prove2me | solution 1 for BalanceSpecification.exists_right_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:53:27.57351+00:00
-- url     : https://prove2.me/submissions/876bdfae-7b86-4444-befa-31f8246e1b87

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_block_append
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {w : Word A} (hw : w ∈ language X) (n : ℕ) :
    ∃ v : Word A, v.length = n ∧ w ++ v ∈ language X := by
  obtain ⟨x, hx, k, hk⟩ := hw
  refine ⟨block x (k + w.length) n, length_block _ _ _, x, hx, k, ?_⟩
  rw [List.length_append, length_block, block_append, hk]
end BalanceSpecification
