-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_rowzero_prejump_geometric_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:30:55.379687+00:00
-- url     : https://prove2.me/submissions/16af9243-b54b-4c62-9eb5-1d1b41e33aef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The zero-time left limit in the literal stopped grid equals its
value because the nonnegative-time order has a bottom element. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x ε : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hzero : X.X 0 ω = 0)
    (hD : rightLimit D 0 ω = x - ε) :
    Function.leftLim (fun t : ℝ≥0 =>
      x + X.X t ω - rightLimit D t ω) 0 = ε := by
  have hbot : IsBot (0 : ℝ≥0) := by
    simpa only [bot_eq_zero] using (isBot_bot : IsBot (⊥ : ℝ≥0))
  rw [leftLim_eq_of_isBot hbot, hzero, hD]
  ring
