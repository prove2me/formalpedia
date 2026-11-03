-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:21:54.717045+00:00
-- url     : https://prove2.me/submissions/2ce91c45-465f-4d17-ab13-c0818d0090ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact strict-survival terminal is killed at and after any ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hRuin : ruinTime X x D ω ≤ (t : ℝ≥0∞)) :
    ∀ s : ℝ≥0, t ≤ s →
      (if (s : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω))
      else 0) = 0 := by
  intro s hts
  have htsENN : (t : ℝ≥0∞) ≤ (s : ℝ≥0∞) := by
    exact_mod_cast hts
  have hNot : ¬ (s : ℝ≥0∞) < ruinTime X x D ω :=
    not_lt_of_ge (hRuin.trans htsENN)
  simp only [if_neg hNot]
