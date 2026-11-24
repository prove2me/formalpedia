-- Prove2me | solution 1 for BalanceSpecification.exists_oneSided_marker_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:03.089807+00:00
-- url     : https://prove2.me/submissions/1e70d815-ab9f-4ca0-a446-319317dd8af1

module
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Definitions.Def_BalanceSpecificaton_MarkedRenewal
public import Definitions.Def_BalanceSpecificaton_MarkerRight
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_MarkerConstruction
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_code_pressure_le_of_exponential_word_bound
public import Theorems.Thm_BalanceSpecification_MarkerExtension_entropy_eq_source_of_upper
public import Theorems.Thm_BalanceSpecification_MarkerExtension_exists_wordCount_exp_bound
public import Theorems.Thm_BalanceSpecification_MarkerExtension_generatedCount_le_pow_of_pressure
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marker_followed_by_word
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marker_synchronizing
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_endingMarkerFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_nonmarker_language
public import Theorems.Thm_BalanceSpecification_MarkerExtension_renamed_source_subset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_rightBalanced_of_marker_extension_bound
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourceCodeFinsetAt_zero
public import Theorems.Thm_BalanceSpecification_biBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_bsm_iff_wordCount_exp_bound
public import Theorems.Thm_BalanceSpecification_codedShift_irreducible
public import Theorems.Thm_BalanceSpecification_exists_sparse_marker_sequence
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_hasSpecification
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_not_leftBalanced_of_marker_extension_exp_bound
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_rightBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.MarkerExtension.mem_endingMarkerFinset
attribute [local simp] BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset
attribute [local simp] BalanceSpecification.MarkerExtension.sourceCodeFinsetAt_zero
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
open MarkerExtension
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)] {Y : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hY : Y.carrier.Nonempty)
    (hSpec : HasSpecification Y) (hentropy : 0 < entropy Y hY) :
    ∃ X : ShiftSpace (Option A), ∃ hX : X.carrier.Nonempty,
      IsCoded X ∧ Irreducible X ∧ entropy X hX = entropy Y hY ∧
      RightBalanced (language X) ∧ ¬LeftBalanced (language X) ∧
      ¬HasVariableSpecification X ∧
      (MarkerEmbedding.renamedShift (some : A → Option A) Y).carrier ⊆ X.carrier := by
  have hYRight := rightBalanced_of_hasVariableSpecification hY
    (hasVariableSpecification_of_hasSpecification hSpec)
  have hBSM := boundedlySupermultiplicative_of_rightBalanced (language_factorial Y) hYRight
  obtain ⟨C, hC, hupperY⟩ := (bsm_iff_wordCount_exp_bound hY).mp hBSM
  obtain ⟨M, hM⟩ := hSpec
  let x : Y.carrier := ⟨Classical.choose hY, Classical.choose_spec hY⟩
  let ρ := Real.exp (entropy Y hY / 2)
  have hρone : 1 < ρ := Real.one_lt_exp_iff.mpr (half_pos hentropy)
  have hρpos : 0 < ρ := zero_lt_one.trans hρone
  have hρsq : ρ ^ 2 = Real.exp (entropy Y hY) := by
    dsimp only [ρ]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  obtain ⟨D, hD, hgrowth, hsizeAll, hbudget, hcofinal⟩ :=
    exists_sparse_marker_sequence hρone hC M
  let s : ℕ → ℕ := fun n => D * 4 ^ n
  have hstrict : StrictMono s := by
    apply strictMono_nat_of_lt_succ
    intro n
    have H := hgrowth n
    change D * 4 ^ n < D * 4 ^ (n + 1)
    omega
  have hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n := fun n _ => hsizeAll n
  have hlarge : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n := by
    intro n hn
    have H := hsize n hn
    omega
  have hupperPow : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * (ρ ^ 2) ^ n := by
    intro n
    rw [hρsq, ← Real.exp_nat_mul]
    exact hupperY n
  have hpressure : ∀ N : ℕ, (∑ l ∈ Finset.range (N + 1),
      (wordCount (code M hM x s) (l + 1) : ℝ) / ρ ^ (l + 1)) ≤ 1 := by
    intro N
    exact (code_pressure_le_of_exponential_word_bound M hM x s hlarge hρpos
      hupperPow hbudget N).trans (by norm_num)
  have hgen : ∀ n : ℕ, (wordCount (generatedWords (code M hM x s)) n : ℝ) ≤ ρ ^ n :=
    generatedCount_le_pow_of_pressure (Set.range (sourcePayload M hM x s)) hρpos hpressure
  have hρlo : Real.exp (entropy Y hY / 4) < ρ :=
    Real.exp_lt_exp.mpr (by linarith only [hentropy])
  have hρhi : ρ < Real.exp (entropy Y hY) :=
    Real.exp_lt_exp.mpr (by linarith only [hentropy])
  obtain ⟨K, hK, hupperX⟩ := exists_wordCount_exp_bound M hM x s hC hupperY
    hstrict hsize hcofinal hρlo hρhi hgen
  let X := shift M hM x s
  have hX : X.carrier.Nonempty := shift_nonempty M hM x s
  have hmarker : IsSynchronizing (language X) [none] := marker_synchronizing M hM x s
  have hF : ∀ v ∈ language Y, [none] ++ v.map some ∈ language X :=
    fun _ hv => marker_followed_by_word M hM x s hv
  have hfree : ∀ u ∈ language X, none ∉ u → ∃ v ∈ language Y, u = v.map some :=
    fun _ hu hnone => nonmarker_language M hM x s hu hnone
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hRight : RightBalanced (language X) :=
    rightBalanced_of_marker_extension_bound hX hY hKpos hupperX hYRight hmarker hF hfree
  have hNotLeft : ¬LeftBalanced (language X) :=
    not_leftBalanced_of_marker_extension_exp_bound hX hY hmarker
      (by simpa only [List.singleton_append] using hF) hKpos hupperX
  refine ⟨X, hX, ⟨code M hM x s, rfl⟩, codedShift_irreducible _,
    entropy_eq_source_of_upper M hM x s hupperX, hRight, hNotLeft, ?_,
    renamed_source_subset M hM x s⟩
  intro hvar
  exact hNotLeft (biBalanced_of_hasVariableSpecification hX hvar).2
end BalanceSpecification
