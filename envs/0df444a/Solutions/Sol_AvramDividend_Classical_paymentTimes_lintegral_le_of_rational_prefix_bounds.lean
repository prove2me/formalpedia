-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_lintegral_le_of_rational_prefix_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:56:57.43132+00:00
-- url     : https://prove2.me/submissions/d55f7a92-2a8a-4662-ad93-7fd2a2afd02c

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_strict_rational_prefixes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-! Directed rational time prefixes preserve any uniform Stieltjes integral bound. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (τ C : ℝ≥0∞)
    (hτ : 0 < τ)
    (hprefix : ∀ q : {q : ℚ // 0 < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < τ},
      (∫⁻ x in Ico (0 : ℝ) (q.val : ℝ), f x ∂μ) ≤ C) :
    (∫⁻ x in paymentTimes τ, f x ∂μ) ≤ C := by
  classical
  let s : {q : ℚ // 0 < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < τ} → Set ℝ :=
    fun q => Ico (0 : ℝ) (q.val : ℝ)
  have hd : Directed (fun a b : Set ℝ => a ⊆ b) s := by
    intro a b
    by_cases hab : a.val ≤ b.val
    · refine ⟨b, ?_, Set.Subset.rfl⟩
      intro x hx
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (by exact_mod_cast hab)⟩
    · refine ⟨a, Set.Subset.rfl, ?_⟩
      intro x hx
      exact ⟨hx.1, lt_of_lt_of_le hx.2
        (by exact_mod_cast (le_of_lt (lt_of_not_ge hab)))⟩
  calc
    (∫⁻ x in paymentTimes τ, f x ∂μ) =
        (∫⁻ x in ⋃ q, s q, f x ∂μ) := by
          rw [paymentTimes_eq_iUnion_strict_rational_prefixes τ hτ]
    _ = ⨆ q, (∫⁻ x in s q, f x ∂μ) :=
      setLIntegral_iUnion_of_directed f hd
    _ ≤ C := iSup_le hprefix
