-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_positive_ruin_openclosed_cash_support_is_strict_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:30:50.535288+00:00
-- url     : https://prove2.me/submissions/36e12151-447e-46f5-8d6a-43c2564b2e30

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_ruin_closed_cash_support_equals_strict
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (σ : ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (hruin : (t : ℝ≥0∞) = σ) (a : ℝ) :
    paymentTimes σ ∩ Ioc a (t : ℝ) =
      paymentTimes σ ∩ Ioo a (t : ℝ) := by
  have hStrict :=
    avram_jump6_B_original_positive_ruin_closed_cash_support_equals_strict
      σ t ht hruin
  ext s
  constructor
  · intro hs
    have hmem : s ∈ paymentTimes σ ∩ Iio (t : ℝ) := by
      rw [← hStrict]
      exact ⟨hs.1, hs.2.2⟩
    exact ⟨hs.1, hs.2.1, hmem.2⟩
  · intro hs
    exact ⟨hs.1, hs.2.1, le_of_lt hs.2.2⟩
