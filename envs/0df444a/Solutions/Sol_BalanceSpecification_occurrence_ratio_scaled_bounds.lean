-- Prove2me | solution 1 for BalanceSpecification.occurrence_ratio_scaled_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:23.633362+00:00
-- url     : https://prove2.me/submissions/ca18d249-1af0-4ecd-b4c1-374bf5f1ad97

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount
public import Theorems.Thm_BalanceSpecification_occurrence_card_le
public import Theorems.Thm_BalanceSpecification_occurrence_card_lower
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    {cL cR C : ℝ} (hcL : 0 ≤ cL) (hcR : 0 ≤ cR) (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy X hX))
    (hR : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cR * (wordCount (language X) n : ℝ) ≤ (followerFinset (language X) u n).card)
    (hP : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cL * (wordCount (language X) n : ℝ) ≤ (predecessorFinset (language X) u n).card)
    {u : Word A} (hu : u ∈ language X) {a b M : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : M = a + u.length + b) :
    cL * cR / C ≤ ((occurrenceFinset (language X) u a b).card : ℝ) /
        wordCount (language X) M * Real.exp ((u.length : ℝ) * entropy X hX) ∧
    ((occurrenceFinset (language X) u a b).card : ℝ) /
        wordCount (language X) M * Real.exp ((u.length : ℝ) * entropy X hX) ≤ C * C := by
  let h := entropy X hX
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hclcr : 0 ≤ cL * cR := mul_nonneg hcL hcR
  have htot : (0 : ℝ) < wordCount (language X) M := by
    exact_mod_cast wordCount_pos_of_nonempty hX M
  have hexp : Real.exp ((M : ℝ) * h) =
      Real.exp ((a : ℝ) * h) * Real.exp ((u.length : ℝ) * h) * Real.exp ((b : ℝ) * h) := by
    rw [hM, Nat.cast_add, Nat.cast_add, add_mul, add_mul, Real.exp_add, Real.exp_add]
  have hnumlow : cL * cR * Real.exp ((a : ℝ) * h) * Real.exp ((b : ℝ) * h) ≤
      ((occurrenceFinset (language X) u a b).card : ℝ) := by
    calc
      cL * cR * Real.exp ((a : ℝ) * h) * Real.exp ((b : ℝ) * h) ≤
          cL * cR * (wordCount (language X) a : ℝ) * wordCount (language X) b :=
        mul_le_mul (mul_le_mul_of_nonneg_left (exp_mul_entropy_le_wordCount hX a) hclcr)
          (exp_mul_entropy_le_wordCount hX b) (Real.exp_nonneg _)
          (mul_nonneg hclcr (Nat.cast_nonneg _))
      _ ≤ _ := occurrence_card_lower hcR (fun v hv => hR v hv b hb) (hP u hu a ha)
  have hnumup : ((occurrenceFinset (language X) u a b).card : ℝ) ≤
      (C * Real.exp ((a : ℝ) * h)) * (C * Real.exp ((b : ℝ) * h)) := by
    calc
      ((occurrenceFinset (language X) u a b).card : ℝ) ≤
          (wordCount (language X) a : ℝ) * wordCount (language X) b := by
        exact_mod_cast occurrence_card_le (L := language X) u a b
      _ ≤ _ := mul_le_mul (hupper a) (hupper b) (Nat.cast_nonneg _)
        (mul_nonneg hCp.le (Real.exp_nonneg _))
  constructor
  · calc
      cL * cR / C =
          (cL * cR * Real.exp ((a : ℝ) * h) * Real.exp ((b : ℝ) * h)) /
            (C * Real.exp ((M : ℝ) * h)) * Real.exp ((u.length : ℝ) * h) := by
        rw [hexp]
        field_simp [hCp.ne', Real.exp_ne_zero]
      _ ≤ ((occurrenceFinset (language X) u a b).card : ℝ) /
          (C * Real.exp ((M : ℝ) * h)) * Real.exp ((u.length : ℝ) * h) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hnumlow (mul_nonneg hCp.le (Real.exp_nonneg _)))
          (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) htot (hupper M)) (Real.exp_nonneg _)
  · calc
      ((occurrenceFinset (language X) u a b).card : ℝ) /
          wordCount (language X) M * Real.exp ((u.length : ℝ) * h) ≤
          ((C * Real.exp ((a : ℝ) * h)) * (C * Real.exp ((b : ℝ) * h))) /
            wordCount (language X) M * Real.exp ((u.length : ℝ) * h) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnumup htot.le)
          (Real.exp_nonneg _)
      _ ≤ ((C * Real.exp ((a : ℝ) * h)) * (C * Real.exp ((b : ℝ) * h))) /
            Real.exp ((M : ℝ) * h) * Real.exp ((u.length : ℝ) * h) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hCp.le (Real.exp_nonneg _))
              (mul_nonneg hCp.le (Real.exp_nonneg _)))
            (Real.exp_pos _) (exp_mul_entropy_le_wordCount hX M)) (Real.exp_nonneg _)
      _ = C * C := by
        rw [hexp]
        field_simp [Real.exp_ne_zero]
end BalanceSpecification
