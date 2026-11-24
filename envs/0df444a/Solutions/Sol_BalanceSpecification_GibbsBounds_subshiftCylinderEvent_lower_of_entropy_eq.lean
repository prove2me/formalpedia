-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.subshiftCylinderEvent_lower_of_entropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:21.861814+00:00
-- url     : https://prove2.me/submissions/a5d6aa38-6c0b-4289-b76e-96ba82f1ddb1

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_exp_bounds
public import Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_disjoint_cylinder
public import Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_avoidingLanguage
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_languageShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
variable [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution
    {X Y : ShiftSpace A} {hX : X.carrier.Nonempty} (hY : Y.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hμ : IsInvariant μ) (hYX : Y.carrier ⊆ X.carrier)
    (heq : entropy Y hY = entropy X hX) (n : ℕ) :
    1 / K ≤ (μ : Measure X.carrier).real (subshiftCylinderEvent X Y n) := by
  have hd : Set.PairwiseDisjoint (wordFinset (language Y) (2 * n + 1) : Set (Word A))
      (fun w => cylinder X w (-(n : ℤ))) := by
    intro v hv w hw hvw
    apply disjoint_cylinder X _ hvw
    exact (mem_wordFinset.mp hv).2.trans (mem_wordFinset.mp hw).2.symm
  have hsum : (μ : Measure X.carrier).real (subshiftCylinderEvent X Y n) =
      ∑ w ∈ wordFinset (language Y) (2 * n + 1),
        (μ : Measure X.carrier).real (cylinder X w (-(n : ℤ))) :=
    measureReal_biUnion_finset hd (fun w _ => measurableSet_cylinder X w _)
  rw [hsum]
  let t := ((2 * n + 1 : ℕ) : ℝ) * entropy X hX
  have hcount : Real.exp t ≤ (wordCount (language Y) (2 * n + 1) : ℝ) := by
    simpa only [heq, t] using exp_mul_entropy_le_wordCount hY (2 * n + 1)
  calc
    1 / K = Real.exp t * (Real.exp (-t) / K) := by
      rw [← mul_div_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    _ ≤ (wordCount (language Y) (2 * n + 1) : ℝ) * (Real.exp (-t) / K) :=
      mul_le_mul_of_nonneg_right hcount (div_nonneg (Real.exp_nonneg _) hB.1.le)
    _ = ∑ _w ∈ wordFinset (language Y) (2 * n + 1), Real.exp (-t) / K := by
      simp only [Finset.sum_const, nsmul_eq_mul, wordCount]
    _ ≤ ∑ w ∈ wordFinset (language Y) (2 * n + 1),
        (μ : Measure X.carrier).real (cylinder X w (-(n : ℤ))) := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
      have hwX : w ∈ language X := by
        obtain ⟨x, hx, k, hk⟩ := hwL
        exact ⟨x, hYX hx, k, hk⟩
      rw [hμ.cylinder_real_eq_zero]
      simpa only [hwlen, t] using (hB.cylinder_real_exp_bounds hwX).1
end GibbsBounds
end BalanceSpecification
