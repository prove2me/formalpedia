-- Prove2me | solution 1 for BalanceSpecification.topologicallyMixing_of_word_bridges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:42.14405+00:00
-- url     : https://prove2.me/submissions/f0f580d3-c61e-48a0-91d4-ee4c2dca5ea0

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
public import Theorems.Thm_BalanceSpecification_exists_centered_cylinder_subset_open
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_block_subword
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shiftMap_iterate_val
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
open Set TopologicalSpace
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (hbridge : ∀ u ∈ language X, ∀ v ∈ language X,
      ∃ K : ℕ, ∀ L : ℕ, K ≤ L →
        ∃ w ∈ language X, w.length = L ∧ u ++ w ++ v ∈ language X) :
    TopologicallyMixing X := by
  intro U V hU hV hUne hVne
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨y, hy⟩ := hVne
  obtain ⟨M, u, hu, hulen, _, hcu⟩ := exists_centered_cylinder_subset_open hU hx
  obtain ⟨N, v, hv, hvlen, _, hcv⟩ := exists_centered_cylinder_subset_open hV hy
  obtain ⟨K, hK⟩ := hbridge u hu v hv
  rw [Filter.eventually_atTop]
  refine ⟨M + N + 1 + K, ?_⟩
  intro n hn
  let L := n - (M + N + 1)
  have hLK : K ≤ L := by dsimp only [L]; omega
  obtain ⟨w, _, hwlen, hfull⟩ := hK L hLK
  obtain ⟨z, hz, hzblock⟩ := mem_language_iff_exists_block_zero.mp hfull
  let p : X.carrier := ⟨SymbolicDynamics.FullShift.shift (M : ℤ) z, X.mapsTo (M : ℤ) hz⟩
  refine ⟨p, hcu ?_, hcv ?_⟩
  · change block (SymbolicDynamics.FullShift.shift (M : ℤ) z) (-(M : ℤ)) u.length = u
    rw [block_shift, add_neg_cancel]
    have H := block_subword z 0 [] u (w ++ v)
      (by simpa only [List.nil_append, List.append_assoc] using hzblock)
    simpa only [List.length_nil, Nat.cast_zero, add_zero] using H
  · change block ((shiftMap X)^[n] p).val (-(N : ℤ)) v.length = v
    rw [shiftMap_iterate_val, block_shift]
    change block (SymbolicDynamics.FullShift.shift (M : ℤ) z)
      ((n : ℤ) + -(N : ℤ)) v.length = v
    rw [block_shift]
    have hstart : (M : ℤ) + ((n : ℤ) + -(N : ℤ)) = u.length + w.length := by
      rw [hulen, hwlen]
      dsimp only [L]
      omega
    rw [hstart]
    have H := block_subword z 0 (u ++ w) v []
      (by simpa only [List.append_nil] using hzblock)
    simpa only [List.length_append, Nat.cast_add, zero_add] using H
end BalanceSpecification
