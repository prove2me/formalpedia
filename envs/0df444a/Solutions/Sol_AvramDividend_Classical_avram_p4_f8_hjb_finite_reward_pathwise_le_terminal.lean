-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f8_hjb_finite_reward_pathwise_le_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:42:33.157715+00:00
-- url     : https://prove2.me/submissions/4c9a7126-6f80-4c4d-ae1c-aa7e38c97f4c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_finite_upcross_stop_contact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original upper-exit reward is the stopped terminal value on the upcross event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤)
    (q : ℝ) (hq : 0 < q)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b) (ω : Ω) :
    (if twoSidedExitUpTimeCorrected X (b - 1) ω <
          twoSidedExitDownTimeCorrected X (-1) ω ∧
        twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (twoSidedExitUpTimeCorrected X (b - 1) ω))) * w b) else 0) ≤
    ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
      (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω)
          (n : ℝ≥0∞))))) *
      w (1 + X.X (ENNReal.toNNReal
        (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω)
            (n : ℝ≥0∞)))) ω)) := by
  let u := twoSidedExitUpTimeCorrected X (b - 1) ω
  let d := twoSidedExitDownTimeCorrected X (-1) ω
  by_cases he : u < d ∧ u ≤ (n : ℝ≥0∞)
  · have hclock : min u (min d (n : ℝ≥0∞)) = u :=
      min_eq_left (le_min he.1.le he.2)
    have hc := avram_p4_f7_hjb_finite_upcross_stop_contact
      X hX b n hb ω he
    have hres :
        1 + X.X (ENNReal.toNNReal (min u (min d (n : ℝ≥0∞)))) ω = b := by
      rw [hc]
      ring
    have hres' : 1 + X.X (ENNReal.toNNReal u) ω = b := by
      simpa only [hclock] using hres
    simp [u, d, he, hclock, hres']
  · simp [u, d, he]
