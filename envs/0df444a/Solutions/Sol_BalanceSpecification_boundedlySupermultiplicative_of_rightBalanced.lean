-- Prove2me | solution 1 for BalanceSpecification.boundedlySupermultiplicative_of_rightBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:01.804174+00:00
-- url     : https://prove2.me/submissions/da04e125-f5fa-45ef-a107-610216dc7959

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Theorems.Thm_BalanceSpecification_wordCount_add_eq_sum_followers
public import Theorems.Thm_BalanceSpecification_wordCount_zero_le_one
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (hL : IsFactorial L)
    (h : RightBalanced L) : BoundedlySupermultiplicative L := by
  classical
  obtain ⟨c, hc, hbound⟩ := h
  refine ⟨max 1 c⁻¹, le_max_left _ _, ?_⟩
  intro m n
  have hcounts : ∀ k, (0 : ℝ) ≤ wordCount L k := fun k => Nat.cast_nonneg _
  by_cases hn : n = 0
  · subst n
    simp only [add_zero]
    have hzero : (wordCount L 0 : ℝ) ≤ 1 := by exact_mod_cast wordCount_zero_le_one L
    calc
      (wordCount L m : ℝ) * wordCount L 0 ≤ (wordCount L m : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hzero (hcounts m)
      _ ≤ max 1 c⁻¹ * wordCount L m := by
        simpa only [mul_one, one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left 1 c⁻¹) (hcounts m)
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hterm : ∀ u ∈ wordFinset L m,
        c * wordCount L n ≤ ((followerFinset L u n).card : ℝ) := by
      intro u hu
      by_cases hzero : wordCount L n = 0
      · simp only [hzero, Nat.cast_zero, mul_zero]
        exact Nat.cast_nonneg _
      · have hpos : (0 : ℝ) < wordCount L n := by
          exact_mod_cast Nat.pos_of_ne_zero hzero
        exact (le_div_iff₀ hpos).mp (hbound u (mem_wordFinset.mp hu).1 n hnpos)
    have hsum := Finset.sum_le_sum hterm
    have htotal : c * ((wordCount L m : ℝ) * wordCount L n) ≤ wordCount L (m + n) := by
      have hsum' : ∑ u ∈ wordFinset L m, c * (wordCount L n : ℝ) ≤
          ∑ u ∈ wordFinset L m, ((followerFinset L u n).card : ℝ) := hsum
      rw [← Nat.cast_sum, ← wordCount_add_eq_sum_followers hL m n] at hsum'
      simpa only [Finset.sum_const, nsmul_eq_mul, wordCount, mul_left_comm] using hsum'
    calc
      (wordCount L m : ℝ) * wordCount L n ≤ c⁻¹ * wordCount L (m + n) := by
        have hh := mul_le_mul_of_nonneg_left htotal (le_of_lt (inv_pos.mpr hc))
        simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh
      _ ≤ max 1 c⁻¹ * wordCount L (m + n) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (hcounts (m + n))
end BalanceSpecification
