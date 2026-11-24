-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.bad_predecessor_mem_crossing_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:31.315995+00:00
-- url     : https://prove2.me/submissions/46392014-0955-483c-bbdb-6f623767bd33

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_prefix_mem_initialObstructions
public import Theorems.Thm_BalanceSpecification_FiveSymbol_mem_language_iff_avoids
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {u v : Word Alphabet}
    (hu : u ∈ language shift) (hv : v ∈ language shift)
    (hbad : v ++ u ∉ language shift) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ v.length ∧ v ∈ leftCrossingCover v.length l := by
  have hex : ∃ j : ℕ, 1 ≤ j ∧ forbiddenWord j <:+: v ++ u := by
    by_contra h
    push Not at h
    exact hbad ((mem_language_iff_avoids _).mpr h)
  obtain ⟨j, hj, hocc⟩ := hex
  rcases List.infix_append_iff_ne_nil.mp hocc with hleft | hright | hcross
  · exact ((mem_language_iff_avoids _).mp hv j hj hleft).elim
  · exact ((mem_language_iff_avoids _).mp hu j hj hright).elim
  · obtain ⟨s, q, hsne, _, hf, hs, _⟩ := hcross
    have hspos : 0 < s.length := List.length_pos_iff.mpr hsne
    have hsn : s.length ≤ v.length := hs.length_le
    have hsforbid : s <+: forbiddenWord j := by
      rw [hf]
      exact List.prefix_append s q
    obtain ⟨t, hts⟩ := hs
    have ht : t ∈ language shift := by
      apply language_factorial shift (List.prefix_append t s).isInfix
      simpa only [hts] using hv
    have htlen : t.length = v.length - s.length := by
      have H := congrArg List.length hts
      simp only [List.length_append] at H
      omega
    refine ⟨s.length, hspos, hsn, Finset.mem_biUnion.mpr ?_⟩
    refine ⟨s, prefix_mem_initialObstructions hsforbid rfl hspos, ?_⟩
    exact Finset.mem_image.mpr ⟨t, mem_wordFinset.mpr ⟨ht, htlen⟩, hts⟩
end BalanceSpecification.FiveSymbol
