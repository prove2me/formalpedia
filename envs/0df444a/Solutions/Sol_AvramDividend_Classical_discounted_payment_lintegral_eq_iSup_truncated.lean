-- Prove2me | solution 1 for AvramDividend.Classical.discounted_payment_lintegral_eq_iSup_truncated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:22:02.187637+00:00
-- url     : https://prove2.me/submissions/93852863-6824-4d6a-a7db-5e66a276e8a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (q : ℝ) (σ : ℝ≥0∞) (μ : Measure ℝ) :
    (∫⁻ t in paymentTimes σ, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      ⨆ n : ℕ, ∫⁻ t in paymentTimes σ ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := by
  let s : ℕ → Set ℝ := fun n => paymentTimes σ ∩ Iic (n : ℝ)
  have hd : Directed (· ⊆ ·) s := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro t ht
      have hij : (i : ℝ) ≤ ((max i j : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_left i j
      exact ⟨ht.1, le_trans ht.2 hij⟩
    · intro t ht
      have hj : (j : ℝ) ≤ ((max i j : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_max_right i j
      exact ⟨ht.1, le_trans ht.2 hj⟩
  calc
    (∫⁻ t in paymentTimes σ, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
        ∫⁻ t in ⋃ n, s n, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := by
          rw [paymentTimes_eq_iUnion_truncated σ]
    _ = ⨆ n, ∫⁻ t in s n, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ :=
      MeasureTheory.setLIntegral_iUnion_of_directed _ hd
    _ = ⨆ n : ℕ, ∫⁻ t in paymentTimes σ ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := by rfl
