-- Prove2me | solution 1 for BalanceSpecification.reverse_mem_language_sGapShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:40.187624+00:00
-- url     : https://prove2.me/submissions/10ac84c1-5bca-4213-9f3b-8763a25f9ba3

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_sGapCode_has_nonempty_word
public import Theorems.Thm_BalanceSpecification_generated_sGap_marker_reverse
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_iff


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {w : Word Bool}
    (hw : w ∈ language (sGapShift S)) : w.reverse ∈ language (sGapShift S) := by
  obtain ⟨v, hv, hwv⟩ := language_codedShift_infix_generatedWords hw
  obtain ⟨r, hr, hreverse⟩ := generated_sGap_marker_reverse hv
  obtain ⟨s, hs⟩ := hS
  have hfull : ([true] ++ v.reverse) ++ List.replicate s false ∈ generatedWords (sGapCode S) := by
    rw [hreverse, List.append_assoc]
    exact append_mem_generatedWords hr (mem_generatedWords_of_mem ⟨s, hs, rfl⟩)
  have hvreverse : v.reverse ∈ language (sGapShift S) := by
    apply (mem_language_codedShift_iff (sGapCode_has_nonempty_word ⟨s, hs⟩)).mpr
    exact ⟨([true] ++ v.reverse) ++ List.replicate s false, hfull,
      [true], List.replicate s false, rfl⟩
  exact language_factorial (sGapShift S) hwv.reverse hvreverse
end BalanceSpecification
