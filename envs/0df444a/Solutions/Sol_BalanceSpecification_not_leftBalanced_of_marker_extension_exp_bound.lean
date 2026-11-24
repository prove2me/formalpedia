-- Prove2me | solution 1 for BalanceSpecification.not_leftBalanced_of_marker_extension_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:27.593404+00:00
-- url     : https://prove2.me/submissions/b7d19f10-9cbf-45dc-9300-07645d2befaf

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
public import Theorems.Thm_BalanceSpecification_marker_count_lower_bound_of_leftBalanced
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
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
    {C : ℝ} (hC : 0 < C)
    (hupper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy Y hY)) :
    ¬ LeftBalanced (language X) := by
  intro hleft
  obtain ⟨c, hc, hlower⟩ := marker_count_lower_bound_of_leftBalanced hX hY hs hext hleft
  obtain ⟨n, hn⟩ := exists_nat_gt (C * Real.exp (entropy Y hY) / c)
  have hratio : 0 < C * Real.exp (entropy Y hY) / c :=
    div_pos (mul_pos hC (Real.exp_pos _)) hc
  have hnpos : 1 ≤ n := by
    have hnreal : (0 : ℝ) < n := hratio.trans hn
    have hnnat : 0 < n := by exact_mod_cast hnreal
    omega
  have H := (hlower n hnpos).trans (hupper (n + 1))
  have H' : ((n : ℝ) * c) * Real.exp ((n : ℝ) * entropy Y hY) ≤
      (C * Real.exp (entropy Y hY)) * Real.exp ((n : ℝ) * entropy Y hY) := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add] at H
    simpa only [mul_assoc, mul_comm, mul_left_comm] using H
  have hnc : (n : ℝ) * c ≤ C * Real.exp (entropy Y hY) :=
    (mul_le_mul_iff_left₀ (Real.exp_pos _)).mp H'
  have hbad : C * Real.exp (entropy Y hY) < (n : ℝ) * c :=
    (div_lt_iff₀ hc).mp hn
  exact (not_le_of_gt hbad) hnc
end BalanceSpecification
