-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_positive_n_clipped_clock_pos_iff_ruin_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:25:59.328319+00:00
-- url     : https://prove2.me/submissions/58a2906a-9b65-48a7-9bea-18f6f85b66da

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) :
    (0 < min (ruinTime X x D ω) (n : ℝ≥0∞)) ↔
      (0 < ruinTime X x D ω) := by
  have hnPos : (0 : ℝ≥0∞) < (n : ℝ≥0∞) := by
    exact_mod_cast hn
  simp [lt_min_iff, hnPos]
