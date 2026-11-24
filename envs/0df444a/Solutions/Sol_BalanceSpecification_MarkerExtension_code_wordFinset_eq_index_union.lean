-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.code_wordFinset_eq_index_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:10.782314+00:00
-- url     : https://prove2.me/submissions/0d3079e8-bce1-429d-ad2f-f81d046d8fff

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_sourceCodeFinsetAt
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourceCodeFinsetAt_zero
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourceCodeFinsetAt_mem_code_length
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_length_of_large
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
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) {l N : ℕ} (hlN : l ≤ N) :
    wordFinset (code M hM x s) (l + 1) =
      (Finset.range (N + 1)).biUnion
        (fun n => if s n = l then sourceCodeFinsetAt M hM x s n else ∅) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨⟨v, ⟨u, rfl⟩, rfl⟩, hzlen⟩ := mem_wordFinset.mp hz
    have hun : 1 ≤ u.val.length := u.property.2
    have heq : s u.val.length = l := by
      simp only [List.length_cons, List.length_map,
        sourcePayload_length_of_large M hM x s hs] at hzlen
      omega
    have huN : u.val.length < N + 1 := by
      have H := hs u.val.length hun
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨u.val.length, Finset.mem_range.mpr huN, ?_⟩
    rw [if_pos heq]
    exact (mem_sourceCodeFinsetAt M hM x s).mpr ⟨u, rfl, rfl⟩
  · intro hz
    obtain ⟨n, _, hz⟩ := Finset.mem_biUnion.mp hz
    split_ifs at hz with hn
    · obtain ⟨_, hzcode, hzlen⟩ := sourceCodeFinsetAt_mem_code_length M hM x s hs hz
      exact mem_wordFinset.mpr ⟨hzcode, by simpa only [hn] using hzlen⟩
    · exact False.elim (Finset.notMem_empty z hz)
end BalanceSpecification.MarkerExtension
