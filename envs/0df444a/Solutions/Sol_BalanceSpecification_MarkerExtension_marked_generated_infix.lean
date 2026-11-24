-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.marked_generated_infix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:06.543273+00:00
-- url     : https://prove2.me/submissions/d0550803-c4c5-4ad8-b511-3fc9a775a610

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marker_mem_of_nonempty_prefix
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {P : Set (Word A)} (hP : P.Nonempty)
    {z w : Word (Option A)} (hz : z ∈ generatedWords (markedCode P))
    (hw : none ∉ w) (hinfix : w <:+: z) : ∃ v ∈ P, w <:+: v.map some := by
  by_cases hwnil : w = []
  · obtain ⟨v, hv⟩ := hP
    exact ⟨v, hv, by simp only [hwnil, List.nil_infix]⟩
  obtain ⟨ws, hws, rfl⟩ := hz
  have aux : ∀ ws : List (Word (Option A)), (∀ g ∈ ws, g ∈ markedCode P) →
      w <:+: ws.flatten → ∃ v ∈ P, w <:+: v.map some := by
    intro ws
    induction ws with
    | nil =>
      intro _ h
      exact False.elim (hwnil (List.eq_nil_of_infix_nil h))
    | cons g ws ih =>
      intro hall h
      have htail : ∀ z ∈ ws, z ∈ markedCode P := fun z hz => hall z (List.mem_cons_of_mem _ hz)
      have hg : g ∈ markedCode P := hall g List.mem_cons_self
      simp only [List.flatten_cons] at h
      rcases List.infix_append_iff_ne_nil.mp h with hhead | hrest | ⟨a, b, _, hb, heq, _, hpre⟩
      · obtain ⟨v, hv, rfl⟩ := hg
        rcases List.infix_cons_iff.mp hhead with hp | hp
        · exact False.elim (hw (marker_mem_of_nonempty_prefix hwnil hp))
        · exact ⟨v, hv, hp⟩
      · exact ih htail hrest
      · have hmarker : none ∈ b := by
          cases ws with
          | nil => exact False.elim (hb (List.eq_nil_of_infix_nil hpre.isInfix))
          | cons g' ws' =>
            obtain ⟨v, _, rfl⟩ := htail g' List.mem_cons_self
            apply marker_mem_of_nonempty_prefix hb
            simpa only [List.flatten_cons, List.cons_append] using hpre
        apply False.elim
        apply hw
        rw [heq]
        exact List.mem_append_right a hmarker
  exact aux ws hws hinfix
end BalanceSpecification.MarkerExtension
