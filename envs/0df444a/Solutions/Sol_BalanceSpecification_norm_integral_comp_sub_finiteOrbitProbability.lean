-- Prove2me | solution 1 for BalanceSpecification.norm_integral_comp_sub_finiteOrbitProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:03.674235+00:00
-- url     : https://prove2.me/submissions/7054e129-8520-4b8e-a099-eda4b68df717

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_integral_comp_sub_finiteOrbitProbability
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
    [TopologicalSpace Ω] (f : Ω → Ω) (x : I → Ω) (n : ℕ) (g : Ω →ᵇ ℝ) :
    ‖(∫ y, (g ∘ f) y ∂(finiteOrbitProbability f x n : Measure Ω)) -
        ∫ y, g y ∂(finiteOrbitProbability f x n : Measure Ω)‖ ≤
      2 * ‖g‖ / (n + 1 : ℕ) := by
  rw [integral_comp_sub_finiteOrbitProbability]
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  calc
    ‖(Fintype.card I : ℝ)⁻¹ * ∑ i : I,
        ((n + 1 : ℕ) : ℝ)⁻¹ * (g (f^[n + 1] (x i)) - g (x i))‖
        = (Fintype.card I : ℝ)⁻¹ * ‖∑ i : I,
            ((n + 1 : ℕ) : ℝ)⁻¹ * (g (f^[n + 1] (x i)) - g (x i))‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hcard.le)]
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i : I,
        ‖((n + 1 : ℕ) : ℝ)⁻¹ * (g (f^[n + 1] (x i)) - g (x i))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _i : I, ((n + 1 : ℕ) : ℝ)⁻¹ * (2 * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hcard.le)
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      exact (norm_sub_le _ _).trans (by
        have h1 := g.norm_coe_le_norm (f^[n + 1] (x i))
        have h2 := g.norm_coe_le_norm (x i)
        linarith only [h1, h2])
    _ = 2 * ‖g‖ / (n + 1 : ℕ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
end BalanceSpecification
