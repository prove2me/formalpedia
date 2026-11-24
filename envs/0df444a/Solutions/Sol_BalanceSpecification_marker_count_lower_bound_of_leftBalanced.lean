-- Prove2me | solution 1 for BalanceSpecification.marker_count_lower_bound_of_leftBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:18.949591+00:00
-- url     : https://prove2.me/submissions/e3785bc0-4a42-4ea2-bb92-709e3e6d52cc

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
public import Theorems.Thm_BalanceSpecification_markerPair_count_le
public import Theorems.Thm_BalanceSpecification_wordCount_le_of_marker_extension
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
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
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]
namespace BalanceSpecification
theorem _root_.solution
    {X : ShiftSpace (Option A)} {Y : ShiftSpace A}
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty)
    (hs : IsSynchronizing (language X) [none])
    (hext : ∀ v ∈ language Y, none :: v.map some ∈ language X)
    (hleft : LeftBalanced (language X)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * c * Real.exp ((n : ℝ) * entropy Y hY) ≤
        wordCount (language X) (n + 1) := by
  obtain ⟨c, hc, hbound⟩ := hleft
  refine ⟨c, hc, ?_⟩
  intro n _hn
  have hterm (k : Fin n) :
      c * Real.exp ((n : ℝ) * entropy Y hY) ≤
        ((predecessorFinset (language X) [none] (k.val + 1)).card : ℝ) *
          wordCount (language Y) (n - 1 - k.val) := by
    have hXpos : (0 : ℝ) < wordCount (language X) (k.val + 1) := by
      exact_mod_cast wordCount_pos_of_nonempty hX (k.val + 1)
    have hp := (le_div_iff₀ hXpos).mp (hbound [none] hs.1 (k.val + 1) (by omega))
    have hemb : (wordCount (language Y) (k.val + 1) : ℝ) ≤
        wordCount (language X) (k.val + 1) := by
      exact_mod_cast wordCount_le_of_marker_extension hext (k.val + 1)
    have hpred : c * Real.exp (((k.val + 1 : ℕ) : ℝ) * entropy Y hY) ≤
        (predecessorFinset (language X) [none] (k.val + 1)).card :=
      (mul_le_mul_of_nonneg_left (exp_mul_entropy_le_wordCount hY _) hc.le).trans
        ((mul_le_mul_of_nonneg_left hemb hc.le).trans hp)
    have hsuff := exp_mul_entropy_le_wordCount hY (n - 1 - k.val)
    have hlength : k.val + 1 + (n - 1 - k.val) = n := by have := k.isLt; omega
    have hexp : Real.exp ((n : ℝ) * entropy Y hY) =
        Real.exp (((k.val + 1 : ℕ) : ℝ) * entropy Y hY) *
          Real.exp (((n - 1 - k.val : ℕ) : ℝ) * entropy Y hY) := by
      rw [← Real.exp_add, ← add_mul, ← Nat.cast_add, hlength]
    calc
      c * Real.exp ((n : ℝ) * entropy Y hY) =
          (c * Real.exp (((k.val + 1 : ℕ) : ℝ) * entropy Y hY)) *
            Real.exp (((n - 1 - k.val : ℕ) : ℝ) * entropy Y hY) := by
        rw [hexp]
        ring
      _ ≤ _ := mul_le_mul hpred hsuff (Real.exp_nonneg _) (Nat.cast_nonneg _)
  have hcount : (∑ k : Fin n,
      ((predecessorFinset (language X) [none] (k.val + 1)).card : ℝ) *
        wordCount (language Y) (n - 1 - k.val)) ≤ wordCount (language X) (n + 1) := by
    exact_mod_cast markerPair_count_le hs hext n
  have H := (Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hterm k)).trans hcount
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc] using H
end BalanceSpecification
