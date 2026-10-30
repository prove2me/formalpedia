-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_rational_open_survival_iff_weak_lower_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:50:22.67175+00:00
-- url     : https://prove2.me/submissions/9bd80612-c273-4ced-bea9-8fcf14e4a228

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_dense_grid_iff
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Countably many open-horizon rational observations detect exactly the weak
extended strict lower passage clock, including the zero/infinite cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (T : ℝ≥0) :
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω) ↔
      (T : ℝ≥0∞) ≤ twoSidedExitDownTime X (-x) ω := by
  rw [← (chat04_random_reserve_lower_survival_dense_grid_iff
    X (fun _ : Ω => x) ω T)]
  constructor
  · intro hSurvive
    unfold twoSidedExitDownTime
    refine le_iInf fun s => ?_
    refine le_iInf fun hs => ?_
    have hTs : T ≤ s := by
      by_contra hn
      have hst : s < T := lt_of_not_ge hn
      have hp := hSurvive s hst
      linarith
    exact ENNReal.coe_le_coe.mpr hTs
  · intro hLower s hst
    by_contra hneg
    have hCross : X.X s ω < -x := by linarith
    have hDownLe :
        twoSidedExitDownTime X (-x) ω ≤ (s : ℝ≥0∞) :=
      twoSidedExitDownTime_le_of_strict_lower_gap_observed
        X x ω s hCross
    have hTs : T ≤ s :=
      ENNReal.coe_le_coe.mp (hLower.trans hDownLe)
    exact (not_lt_of_ge hTs) hst
