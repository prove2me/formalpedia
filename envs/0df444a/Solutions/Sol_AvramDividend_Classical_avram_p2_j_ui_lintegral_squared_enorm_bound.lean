-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_lintegral_squared_enorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:56:10.871412+00:00
-- url     : https://prove2.me/submissions/2eb92394-e635-4342-a44a-b1a557ec8987

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal

/-! A finite ENNReal second lintegral envelope controls the L² seminorm. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (B : ℝ≥0)
    (hB : (∫⁻ ω, ‖Y ω‖ₑ ^ (2 : ℝ) ∂P) ≤ (B : ENNReal) ^ 2) :
    eLpNorm Y 2 P ≤ (B : ENNReal) := by
  have hpow : ((B : ENNReal) ^ 2) ^ (1 / 2 : ℝ) =
      (B : ENNReal) := by
    simpa using
      (ENNReal.rpow_mul (B : ENNReal) 2 (1 / 2 : ℝ)).symm
  calc
    eLpNorm Y 2 P =
        (∫⁻ ω, ‖Y ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
          simpa using
            (eLpNorm_eq_lintegral_rpow_enorm_toReal
              (μ := P) (f := Y) (p := (2 : ENNReal))
              (by norm_num) (by norm_num))
    _ ≤ ((B : ENNReal) ^ 2) ^ (1 / 2 : ℝ) := by
      gcongr
    _ = (B : ENNReal) := hpow
