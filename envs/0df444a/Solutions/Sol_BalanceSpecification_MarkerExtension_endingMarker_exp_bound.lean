-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.endingMarker_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:44.745598+00:00
-- url     : https://prove2.me/submissions/d4ea9afd-ee4b-41b2-b63e-8a93420d592e

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_endingMarkerFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_endingMarker_count_le_convolution
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_payloadSuffix_card_exp_bound
public import Theorems.Thm_BalanceSpecification_convolution_le_geometric_envelope
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
attribute [local simp] BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset
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


attribute [local simp] BalanceSpecification.MarkerExtension.mem_endingMarkerFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {hY : Y.carrier.Nonempty} {C ρ : ℝ}
    (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * Real.exp ((n : ℝ) * entropy Y hY))
    (hstrict : StrictMono s) (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    (hcofinal : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n)
    (hρ : Real.exp (entropy Y hY / 4) < ρ)
    (hgen : ∀ n : ℕ, (wordCount (generatedWords (code M hM x s)) n : ℝ) ≤ ρ ^ n)
    (n : ℕ) :
    ((endingMarkerFinset (shift M hM x s) (n + 1)).card : ℝ) ≤
      (C / (1 - Real.exp (entropy Y hY / 4) / ρ)) * ρ ^ n := by
  have hρpos : 0 < ρ := (Real.exp_pos _).trans hρ
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hsuf : ∀ l : ℕ, ((payloadSuffixFinset M hM x s l).card : ℝ) ≤
      C * (Real.exp (entropy Y hY / 4)) ^ l := by
    intro l
    have H := payloadSuffix_card_exp_bound M hM x s hC0 hupper hstrict hsize hcofinal l
    have heq : Real.exp ((l : ℝ) * entropy Y hY / 4) =
        Real.exp (entropy Y hY / 4) ^ l := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa only [heq] using H
  have hconv := convolution_le_geometric_envelope (Real.exp_nonneg _) hρpos hρ hC0
    (fun l => Nat.cast_nonneg ((payloadSuffixFinset M hM x s l).card)) hsuf hgen n
  have hcount : ((endingMarkerFinset (shift M hM x s) (n + 1)).card : ℝ) ≤
      ∑ l ∈ Finset.range (n + 1), ((payloadSuffixFinset M hM x s l).card : ℝ) *
        (wordCount (generatedWords (code M hM x s)) (n - l) : ℝ) := by
    exact_mod_cast endingMarker_count_le_convolution M hM x s n
  exact hcount.trans hconv
end BalanceSpecification.MarkerExtension
