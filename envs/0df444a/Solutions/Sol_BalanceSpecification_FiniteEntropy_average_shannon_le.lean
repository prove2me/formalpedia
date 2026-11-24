-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.average_shannon_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:35.424936+00:00
-- url     : https://prove2.me/submissions/f181ed54-8d91-4637-9322-0300302e6d35

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_sum_mul_shannon_le
public import Theorems.Thm_BalanceSpecification_cylinder_nil
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
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
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
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
open BalanceSpecification.FiniteEntropy
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution [Nonempty κ] {p : κ → ι → ℝ}
    (hp : ∀ k i, 0 ≤ p k i) :
    (Fintype.card κ : ℝ)⁻¹ * ∑ k, shannon (p k) ≤
      shannon (fun i => (Fintype.card κ : ℝ)⁻¹ * ∑ k, p k i) := by
  have hc : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := sum_mul_shannon_le (w := fun _ : κ => (Fintype.card κ : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ hc) hp
  simpa only [← Finset.mul_sum] using h
end BalanceSpecification.FiniteEntropy
