-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_positive_n_zero_clock_iff_ruin_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:25:50.78569+00:00
-- url     : https://prove2.me/submissions/b6e96eae-450b-4615-953b-1e40fc74f848

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
    (min (ruinTime X x D ω) (n : ℝ≥0∞) = 0) ↔
      (ruinTime X x D ω = 0) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  simpa [ENNReal.min_eq_zero_iff, hn0]
