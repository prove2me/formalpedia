-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f7_hjb_finite_upcross_stop_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:26:32.952196+00:00
-- url     : https://prove2.me/submissions/2ad2a201-d777-4f54-8664-83c03c0dae2d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The clipped original upper-first-passage clock remains the first
upper-passage clock on its successful finite-horizon event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b)
    (ω : Ω)
    (hup :
      twoSidedExitUpTimeCorrected X (b - 1) ω <
        twoSidedExitDownTimeCorrected X (-1) ω ∧
      twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞)) :
    X.X
      (ENNReal.toNNReal
        (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)))) ω =
      b - 1 := by
  rcases hup with ⟨hu, hn⟩
  let u : ℝ≥0∞ := twoSidedExitUpTimeCorrected X (b - 1) ω
  let d : ℝ≥0∞ := twoSidedExitDownTimeCorrected X (-1) ω
  have hclock : min u (min d (n : ℝ≥0∞)) = u := by
    exact min_eq_left (le_min (le_of_lt hu) hn)
  have hfin : u ≠ ⊤ := ne_top_of_le_ne_top (by simp) hn
  have hcast :
      ((ENNReal.toNNReal (min u (min d (n : ℝ≥0∞))) : ℝ≥0) : ℝ≥0∞) =
        twoSidedExitUpTimeCorrected X (b - 1) ω := by
    rw [hclock]
    exact ENNReal.coe_toNNReal hfin
  apply firstUpcrossing_value_eq_threshold X (b - 1) (by linarith) ω _
  simpa only [u, d, twoSidedExitUpTimeCorrected] using hcast
