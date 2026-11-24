-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.bad_follower_mem_crossing_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:37.034544+00:00
-- url     : https://prove2.me/submissions/4a9b5853-d0e3-421a-baa2-9425f9a55afb

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_suffix_mem_terminalObstructions
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
    (hbad : u ++ v ∉ language shift) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ v.length ∧ v ∈ rightCrossingCover v.length l := by
  have hex : ∃ j : ℕ, 1 ≤ j ∧ forbiddenWord j <:+: u ++ v := by
    by_contra h
    push Not at h
    exact hbad ((mem_language_iff_avoids _).mpr h)
  obtain ⟨j, hj, hocc⟩ := hex
  rcases List.infix_append_iff_ne_nil.mp hocc with hleft | hright | hcross
  · exact ((mem_language_iff_avoids _).mp hu j hj hleft).elim
  · exact ((mem_language_iff_avoids _).mp hv j hj hright).elim
  · obtain ⟨p, s, _, hsne, hf, _, hs⟩ := hcross
    have hspos : 0 < s.length := List.length_pos_iff.mpr hsne
    have hsn : s.length ≤ v.length := hs.length_le
    have hsforbid : s <:+ forbiddenWord j := by
      rw [hf]
      exact List.suffix_append p s
    obtain ⟨t, hst⟩ := hs
    have ht : t ∈ language shift := by
      apply language_factorial shift (List.suffix_append s t).isInfix
      simpa only [hst] using hv
    have htlen : t.length = v.length - s.length := by
      have H := congrArg List.length hst
      simp only [List.length_append] at H
      omega
    refine ⟨s.length, hspos, hsn, Finset.mem_biUnion.mpr ?_⟩
    refine ⟨s, suffix_mem_terminalObstructions hsforbid rfl hspos, ?_⟩
    exact Finset.mem_image.mpr ⟨t, mem_wordFinset.mpr ⟨ht, htlen⟩, hst⟩
end BalanceSpecification.FiveSymbol
