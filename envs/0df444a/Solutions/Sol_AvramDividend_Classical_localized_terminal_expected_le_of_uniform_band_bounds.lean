-- Prove2me | solution 1 for AvramDividend.Classical.localized_terminal_expected_le_of_uniform_band_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:49:13.385073+00:00
-- url     : https://prove2.me/submissions/b63d07c7-3ac5-4506-b453-784ad45e44df

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_localized_nonnegative_terminal_lintegral_iSup_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Classical ENNReal

/-- Uniform finite-band expectation bounds extend to every nonnegative reserve. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (r : Ω → ℝ) (hr : Measurable r)
    (w : ℝ → ℝ) (hw : Measurable w)
    (K : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, if ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ) then
        ENNReal.ofReal (w (r ω)) else 0 ∂P) ≤ K) :
    (∫⁻ ω, if ω ∈ A ∧ 0 ≤ r ω then
      ENNReal.ofReal (w (r ω)) else 0 ∂P) ≤ K := by
  rw [AvramDividend.Classical.localized_nonnegative_terminal_lintegral_iSup_bands
    P A hA r hr w hw]
  exact iSup_le hBound
