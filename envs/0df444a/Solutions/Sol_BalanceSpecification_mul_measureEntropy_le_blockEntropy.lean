-- Prove2me | solution 1 for BalanceSpecification.mul_measureEntropy_le_blockEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:52.518538+00:00
-- url     : https://prove2.me/submissions/d9131dd5-d15a-4d6f-997c-e07adfe7b860

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Theorems.Thm_BalanceSpecification_blockEntropy_nonneg
public import Theorems.Thm_BalanceSpecification_measureEntropy_le_blockEntropy_div
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {μ : ProbabilityMeasure X.carrier}
    (hInv : IsInvariant μ) (n : ℕ) :
    (n : ℝ) * measureEntropy μ hInv ≤ blockEntropy μ n := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero, zero_mul] using blockEntropy_nonneg μ 0
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := (le_div_iff₀ hnp).mp (measureEntropy_le_blockEntropy_div hInv hn)
  simpa only [mul_comm] using h
end BalanceSpecification
