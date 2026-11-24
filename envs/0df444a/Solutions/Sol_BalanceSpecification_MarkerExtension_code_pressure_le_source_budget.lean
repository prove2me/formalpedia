-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.code_pressure_le_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:11.306922+00:00
-- url     : https://prove2.me/submissions/927deba3-9262-4540-8af7-c4009e0b874b

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourceCodeFinsetAt_card_le
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourceCodeFinsetAt_zero
public import Theorems.Thm_BalanceSpecification_MarkerExtension_code_wordFinset_eq_index_union
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


attribute [local simp] BalanceSpecification.MarkerExtension.sourceCodeFinsetAt_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
open scoped Classical
variable {A : Type*} [TopologicalSpace A] [Fintype A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) :
    (∑ l ∈ Finset.range (N + 1),
      (wordCount (code M hM x s) (l + 1) : ℝ) / ρ ^ (l + 1)) ≤
      ∑ n ∈ Finset.range (N + 1),
        if 1 ≤ n then (wordCount (language Y) n : ℝ) / ρ ^ (s n + 1) else 0 := by
  classical
  let W : ℕ → ℝ := fun n =>
    if 1 ≤ n then (wordCount (language Y) n : ℝ) / ρ ^ (s n + 1) else 0
  have hW (n : ℕ) : 0 ≤ W n := by
    dsimp only [W]
    split
    · exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ.le _)
    · exact le_refl _
  have hterm (l : ℕ) (hl : l ≤ N) :
      (wordCount (code M hM x s) (l + 1) : ℝ) / ρ ^ (l + 1) ≤
        ∑ n ∈ Finset.range (N + 1), if s n = l then W n else 0 := by
    have hcard : wordCount (code M hM x s) (l + 1) ≤
        ∑ n ∈ Finset.range (N + 1),
          (if s n = l then sourceCodeFinsetAt M hM x s n else ∅).card := by
      unfold wordCount
      rw [code_wordFinset_eq_index_union M hM x s hs hl]
      exact Finset.card_biUnion_le
    have hcardR : (wordCount (code M hM x s) (l + 1) : ℝ) ≤
        ∑ n ∈ Finset.range (N + 1),
          ((if s n = l then sourceCodeFinsetAt M hM x s n else ∅).card : ℝ) := by
      exact_mod_cast hcard
    calc
      _ ≤ (∑ n ∈ Finset.range (N + 1),
          ((if s n = l then sourceCodeFinsetAt M hM x s n else ∅).card : ℝ)) /
            ρ ^ (l + 1) := div_le_div_of_nonneg_right hcardR (pow_nonneg hρ.le _)
      _ = ∑ n ∈ Finset.range (N + 1),
          ((if s n = l then sourceCodeFinsetAt M hM x s n else ∅).card : ℝ) /
            ρ ^ (l + 1) := Finset.sum_div _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hnl : s n = l
        · rw [if_pos hnl, if_pos hnl]
          by_cases hn : 1 ≤ n
          · dsimp only [W]
            rw [if_pos hn, hnl]
            apply div_le_div_of_nonneg_right _ (pow_nonneg hρ.le _)
            exact_mod_cast sourceCodeFinsetAt_card_le M hM x s n
          · have hn0 : n = 0 := by omega
            subst n
            simp only [sourceCodeFinsetAt_zero, Finset.card_empty, Nat.cast_zero,
              zero_div, W, hn, ite_false, le_refl]
        · rw [if_neg hnl, if_neg hnl]
          simp only [Finset.card_empty, Nat.cast_zero, zero_div, le_refl]
  calc
    _ ≤ ∑ l ∈ Finset.range (N + 1),
        ∑ n ∈ Finset.range (N + 1), if s n = l then W n else 0 :=
      Finset.sum_le_sum (fun l hl => hterm l (by have := Finset.mem_range.mp hl; omega))
    _ = ∑ n ∈ Finset.range (N + 1),
        ∑ l ∈ Finset.range (N + 1), if s n = l then W n else 0 := Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.range (N + 1), W n := by
      apply Finset.sum_le_sum
      intro n _
      rw [Finset.sum_ite_eq]
      split
      · exact le_refl _
      · exact hW n
end BalanceSpecification.MarkerExtension
