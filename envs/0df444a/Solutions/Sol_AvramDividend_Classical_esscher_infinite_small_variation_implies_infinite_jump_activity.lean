-- Prove2me | solution 1 for AvramDividend.Classical.esscher_infinite_small_variation_implies_infinite_jump_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:28:38.258495+00:00
-- url     : https://prove2.me/submissions/dc952ca1-03f6-4ca8-b852-3850a9966bef

import Theorems.Thm_AvramDividend_Classical_esscher_preserves_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_infinite_small_jump_moment_implies_infinite_negative_activity
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂ν) = ⊤) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (0 : ℝ)) = ⊤ := by
  exact infinite_small_jump_moment_implies_infinite_negative_activity
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
    (esscher_preserves_infinite_small_jump_moment ν φ hφ hvar)
