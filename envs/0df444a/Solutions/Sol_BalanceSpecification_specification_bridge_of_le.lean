-- Prove2me | solution 1 for BalanceSpecification.specification_bridge_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:15.508643+00:00
-- url     : https://prove2.me/submissions/f412b93f-5833-4e9e-90e7-714ccf873e6e

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_exists_right_extension
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A] {X : ShiftSpace A}
    {N M : ℕ}
    (hN : ∀ u ∈ language X, ∀ v ∈ language X,
      ∃ w ∈ language X, w.length = N ∧ u ++ w ++ v ∈ language X)
    (hNM : N ≤ M) :
    ∀ u ∈ language X, ∀ v ∈ language X,
      ∃ w ∈ language X, w.length = M ∧ u ++ w ++ v ∈ language X := by
  intro u hu v hv
  obtain ⟨t, htlen, hut⟩ := exists_right_extension hu (M - N)
  obtain ⟨w, _, hwlen, hutwv⟩ := hN (u ++ t) hut v hv
  have hfull : u ++ (t ++ w) ++ v ∈ language X := by
    simpa only [List.append_assoc] using hutwv
  refine ⟨t ++ w, language_factorial X (u := t ++ w) (v := u ++ (t ++ w) ++ v)
    ⟨u, v, rfl⟩ hfull, ?_, hfull⟩
  simp only [List.length_append, htlen, hwlen]
  omega
end BalanceSpecification
