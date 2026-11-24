-- Prove2me | solution 1 for BalanceSpecification.exists_two_sided_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:44.058256+00:00
-- url     : https://prove2.me/submissions/45ba6bc4-d1af-4eb3-8723-5475bc686f39

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_exists_right_extension
public import Theorems.Thm_BalanceSpecification_exists_left_extension
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {w : Word A} (hw : w ∈ language X) (m n : ℕ) :
    ∃ u v : Word A, u.length = m ∧ v.length = n ∧ u ++ w ++ v ∈ language X := by
  obtain ⟨v, hv, hwv⟩ := exists_right_extension hw n
  obtain ⟨u, hu, huwv⟩ := exists_left_extension hwv m
  exact ⟨u, v, hu, hv, by simpa only [List.append_assoc] using huwv⟩
end BalanceSpecification
