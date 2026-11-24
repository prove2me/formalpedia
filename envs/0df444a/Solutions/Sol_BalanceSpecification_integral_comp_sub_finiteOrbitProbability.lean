-- Prove2me | solution 1 for BalanceSpecification.integral_comp_sub_finiteOrbitProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:02.91935+00:00
-- url     : https://prove2.me/submissions/cba4cb3c-ceed-4aa7-83ec-f1df892506f0

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_integral_finiteOrbitProbability
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
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
namespace BalanceSpecification
theorem _root_.solution [MeasurableSingletonClass Ω]
    (f : Ω → Ω) (x : I → Ω) (n : ℕ) (g : Ω → ℝ) :
    (∫ y, (g ∘ f) y ∂(finiteOrbitProbability f x n : Measure Ω)) -
        ∫ y, g y ∂(finiteOrbitProbability f x n : Measure Ω) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i : I,
        ((n + 1 : ℕ) : ℝ)⁻¹ * (g (f^[n + 1] (x i)) - g (x i)) := by
  rw [integral_finiteOrbitProbability, integral_finiteOrbitProbability, ← mul_sub,
    ← Finset.sum_sub_distrib]
  apply congrArg ((Fintype.card I : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro i _
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, Function.comp_apply, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  have htel : ∀ k, g (f (f^[k] (x i))) = g (f^[k + 1] (x i)) :=
    fun k => by rw [Function.iterate_succ_apply']
  simp_rw [htel]
  simpa [Function.iterate_zero_apply] using
    Finset.sum_range_sub (fun k => g (f^[k] (x i))) (n + 1)
end BalanceSpecification
