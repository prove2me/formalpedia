-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_levy_weighted_mark_cutoff_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:17:16.229407+00:00
-- url     : https://prove2.me/submissions/6e6f24a1-8a3a-44fc-a59b-38b1b02a8c88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original source Levy intensity integral of a constant nonnegative
mark weight is continuous from below along increasing measurable cutoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hB : ∀ n, MeasurableSet (B n)) (c : ℝ≥0∞) :
    (∫⁻ z : ℝ, (⋃ n, B n).indicator (fun _ => c) z ∂X.ν) =
      ⨆ n, (∫⁻ z : ℝ, (B n).indicator (fun _ => c) z ∂X.ν) := by
  have hUnion : MeasurableSet (⋃ n, B n) :=
    MeasurableSet.iUnion hB
  calc
    _ = c * X.ν (⋃ n, B n) :=
      lintegral_indicator_const hUnion c
    _ = c * (⨆ n, X.ν (B n)) := by rw [hMon.measure_iUnion]
    _ = ⨆ n, c * X.ν (B n) := by rw [ENNReal.mul_iSup]
    _ = _ := by
      apply iSup_congr
      intro n
      exact (lintegral_indicator_const (hB n) c).symm
