-- Prove2me | solution 1 for BalanceSpecification.rate_languageShift_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:15.667253+00:00
-- url     : https://prove2.me/submissions/77bede20-3855-4a54-9223-4b16f8acb46a

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_language_languageShift_subset
public import Theorems.Thm_BalanceSpecification_exists_interior_subset_languageShift
public import Theorems.Thm_BalanceSpecification_nonempty_languageShift_of_words_all_lengths
public import Theorems.Thm_BalanceSpecification_Growth_rate_le_of_tiling_bounds
public import Theorems.Thm_BalanceSpecification_Growth_rate_mono
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_add_le
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative
public import Theorems.Thm_BalanceSpecification_wordCount_tiling_le
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_languageShift_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} (hL : IsFactorial L)
    (hpos : ∀ n, 0 < wordCount L n) :
    Growth.rate (fun n => (wordCount L n : ℝ)) =
      Growth.rate (fun n => (wordCount (language (languageShift L)) n : ℝ)) := by
  classical
  have hA : Nonempty A := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (hpos 1)
    have hlen := (mem_wordFinset.mp hw).2
    cases w with
    | nil => simp only [List.length_nil, Nat.zero_ne_one] at hlen
    | cons a l => exact ⟨a⟩
  let : Nonempty A := hA
  have hcore : (languageShift L).carrier.Nonempty :=
    nonempty_languageShift_of_words_all_lengths hL (by
      intro n
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (hpos n)
      exact ⟨w, (mem_wordFinset.mp hw).1, (mem_wordFinset.mp hw).2⟩)
  have ha : ∀ n, (1 : ℝ) ≤ wordCount L n := fun n => by exact_mod_cast hpos n
  have hb := wordCount_one_le hcore
  have hsa : Submultiplicative (fun n => (wordCount L n : ℝ)) := by
    intro m n
    change (wordCount L (m + n) : ℝ) ≤ (wordCount L m : ℝ) * (wordCount L n : ℝ)
    exact_mod_cast wordCount_add_le hL m n
  have hsb := wordCount_submultiplicative (languageShift L)
  apply le_antisymm
  · apply Growth.rate_le_of_tiling_bounds ha hb hsa
    intro n hn
    obtain ⟨M, hM⟩ := exists_interior_subset_languageShift hL n
    refine ⟨M, (Fintype.card A : ℝ) ^ (2 * M), ?_, ?_⟩
    · exact pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    · intro k
      exact_mod_cast wordCount_tiling_le hL M n k hM
  · apply Growth.rate_mono hb ha hsb hsa
    intro n
    exact_mod_cast (show wordCount (language (languageShift L)) n ≤ wordCount L n from
      Finset.card_le_card (by
        intro w hw
        obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
        exact mem_wordFinset.mpr ⟨language_languageShift_subset L hwL, hwlen⟩))
end BalanceSpecification
