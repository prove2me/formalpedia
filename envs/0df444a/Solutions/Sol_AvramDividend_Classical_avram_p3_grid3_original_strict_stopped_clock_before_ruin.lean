-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_strict_stopped_clock_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:04:55.369871+00:00
-- url     : https://prove2.me/submissions/a73c0841-4ceb-4d9e-a711-e8edec4d2878

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (s : ℝ≥0)
    (hs : s < (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) :
    (s : ℝ≥0∞) < ruinTime X x D ω := by
  let r : ℝ≥0∞ := min (ruinTime X x D ω) (T : ℝ≥0∞)
  have hfinite : r < ⊤ := by
    exact lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top
  have hco : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) = r :=
    ENNReal.coe_toNNReal (ne_of_lt hfinite)
  have hs' : (s : ℝ≥0∞) < ((r.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hs
  calc
    (s : ℝ≥0∞) < r := by simpa only [hco] using hs'
    _ ≤ ruinTime X x D ω := min_le_left _ _
