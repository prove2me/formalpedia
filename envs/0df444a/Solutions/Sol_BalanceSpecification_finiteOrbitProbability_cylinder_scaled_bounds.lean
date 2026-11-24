-- Prove2me | solution 1 for BalanceSpecification.finiteOrbitProbability_cylinder_scaled_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:05.011564+00:00
-- url     : https://prove2.me/submissions/da30871b-3292-4f9d-9fea-ba12382fd69c

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_finiteOrbitProbability_real_apply
public import Theorems.Thm_BalanceSpecification_finitePointProbability_cylinder_real_of_length
public import Theorems.Thm_BalanceSpecification_occurrence_ratio_scaled_bounds
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
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
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    {cL cR C : ℝ} (hcL : 0 ≤ cL) (hcR : 0 ≤ cR) (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy X hX))
    (hR : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cR * (wordCount (language X) n : ℝ) ≤ (followerFinset (language X) u n).card)
    (hP : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cL * (wordCount (language X) n : ℝ) ≤ (predecessorFinset (language X) u n).card)
    (n : ℕ) [Nonempty ↥(wordFinset (language X) (3 * (n + 1)))]
    (x : ↥(wordFinset (language X) (3 * (n + 1))) → X.carrier)
    (hx : ∀ w, block (x w).val 0 (3 * (n + 1)) = w.val)
    {u : Word A} (hu : u ∈ language X) (hlen : u.length ≤ n + 1) :
    cL * cR / C ≤
        (finiteOrbitProbability (shiftMap X) (fun w => (shiftMap X)^[n + 1] (x w)) n :
          Measure X.carrier).real (cylinder X u 0) *
            Real.exp ((u.length : ℝ) * entropy X hX) ∧
    (finiteOrbitProbability (shiftMap X) (fun w => (shiftMap X)^[n + 1] (x w)) n :
          Measure X.carrier).real (cylinder X u 0) *
            Real.exp ((u.length : ℝ) * entropy X hX) ≤ C * C := by
  let E := Real.exp ((u.length : ℝ) * entropy X hX)
  let P : Fin (n + 1) → ℝ := fun j =>
    (finitePointProbability (fun w =>
      (shiftMap X)^[j.val] ((shiftMap X)^[n + 1] (x w))) : Measure X.carrier).real
        (cylinder X u 0) * E
  have hj (j : Fin (n + 1)) : cL * cR / C ≤ P j ∧ P j ≤ C * C := by
    let a := n + 1 + j.val
    let b := 3 * (n + 1) - a - u.length
    have ha : 1 ≤ a := by dsimp only [a]; omega
    have hb : 1 ≤ b := by dsimp only [b, a]; omega
    have hM : 3 * (n + 1) = a + u.length + b := by dsimp only [b, a]; omega
    have hfun : (fun w => (shiftMap X)^[j.val] ((shiftMap X)^[n + 1] (x w))) =
        (fun w => (shiftMap X)^[a] (x w)) := by
      funext w
      dsimp only [a]
      rw [Nat.add_comm (n + 1) j.val]
      exact (Function.iterate_add_apply (shiftMap X) j.val (n + 1) (x w)).symm
    dsimp only [P]
    rw [hfun, finitePointProbability_cylinder_real_of_length u a b hM x hx]
    exact occurrence_ratio_scaled_bounds hX hcL hcR hC hupper hR hP hu ha hb hM
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have heval :
      (finiteOrbitProbability (shiftMap X) (fun w => (shiftMap X)^[n + 1] (x w)) n :
        Measure X.carrier).real (cylinder X u 0) * E =
        ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (n + 1), P j := by
    rw [finiteOrbitProbability_real_apply _ _ _ (measurableSet_cylinder X u 0)]
    simp only [P, Finset.sum_mul, mul_assoc]
  change cL * cR / C ≤ _ * E ∧ _ * E ≤ C * C
  rw [heval]
  constructor
  · calc
      cL * cR / C = ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _j : Fin (n + 1), cL * cR / C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ => (hj j).1) (inv_nonneg.mpr hn.le)
  · calc
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (n + 1), P j ≤
          ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _j : Fin (n + 1), C * C :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => (hj j).2)
          (inv_nonneg.mpr hn.le)
      _ = C * C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
end BalanceSpecification
