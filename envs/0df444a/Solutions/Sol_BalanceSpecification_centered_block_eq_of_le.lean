-- Prove2me | solution 1 for BalanceSpecification.centered_block_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:58.004216+00:00
-- url     : https://prove2.me/submissions/71da3aa5-765c-41c7-9d6e-9fe40303b924

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
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
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {n N : ℕ} (hn : n ≤ N)
    {x y : Configuration A}
    (h : block x (-(N : ℤ)) (2 * N + 1) =
      block y (-(N : ℤ)) (2 * N + 1)) :
    block x (-(n : ℤ)) (2 * n + 1) = block y (-(n : ℤ)) (2 * n + 1) := by
  apply List.ext_getElem
  · simp only [length_block]
  · intro i hi _
    have hin : i < 2 * n + 1 := by simpa only [length_block] using hi
    let j := N - n + i
    have hj : j < 2 * N + 1 := by dsimp only [j]; omega
    have he := List.getElem_of_eq h
      (show j < (block x (-(N : ℤ)) (2 * N + 1)).length by
        simpa only [length_block] using hj)
    simp only [block, List.getElem_ofFn] at he ⊢
    have hindex : -(N : ℤ) + (j : ℤ) = -(n : ℤ) + (i : ℤ) := by
      dsimp only [j]
      omega
    simpa only [hindex] using he
end BalanceSpecification
