-- Prove2me | solution 1 for BalanceSpecification.exists_left_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:40.797597+00:00
-- url     : https://prove2.me/submissions/6cbfa903-aaf7-406d-b269-e39a8b26f398

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
    ∃ v : Word A, v.length = n ∧ v ++ w ∈ language X := by
  obtain ⟨x, hx, k, hk⟩ := hw
  refine ⟨block x (k - n) n, length_block _ _ _, x, hx, k - n, ?_⟩
  rw [List.length_append, length_block, block_append, sub_add_cancel, hk]
end BalanceSpecification
