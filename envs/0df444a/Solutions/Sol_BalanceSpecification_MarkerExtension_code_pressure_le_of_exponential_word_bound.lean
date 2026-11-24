-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.code_pressure_le_of_exponential_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:08.691802+00:00
-- url     : https://prove2.me/submissions/9dce3fcd-1f23-408a-83ae-4c8169675ed1

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Theorems.Thm_BalanceSpecification_MarkerExtension_code_pressure_le_source_budget

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
open scoped Classical
variable {A : Type*} [TopologicalSpace A] [Fintype A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) {ρ : ℝ} (hρ : 0 < ρ)
    {C growthBase B : ℝ}
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * growthBase ^ n)
    (hbudget : ∀ L : ℕ, (∑ n ∈ Finset.range L,
      if 1 ≤ n then C * growthBase ^ n / ρ ^ (s n + 1) else 0) ≤ B) (N : ℕ) :
    (∑ l ∈ Finset.range (N + 1),
      (wordCount (code M hM x s) (l + 1) : ℝ) / ρ ^ (l + 1)) ≤ B := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        if 1 ≤ n then (wordCount (language Y) n : ℝ) / ρ ^ (s n + 1) else 0 :=
      code_pressure_le_source_budget M hM x s hs hρ N
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        if 1 ≤ n then C * growthBase ^ n / ρ ^ (s n + 1) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      split
      · exact div_le_div_of_nonneg_right (hupper n) (pow_nonneg hρ.le _)
      · exact le_refl _
    _ ≤ B := hbudget (N + 1)
end BalanceSpecification.MarkerExtension
