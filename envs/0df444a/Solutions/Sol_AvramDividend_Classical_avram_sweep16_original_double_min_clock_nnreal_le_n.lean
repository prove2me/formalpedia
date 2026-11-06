-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_double_min_clock_nnreal_le_n
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:29:00.153364+00:00
-- url     : https://prove2.me/submissions/62e23864-2fcf-48c6-8acc-137709d9fa0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-! All localised NNReal source clocks stay below the finite real horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (S : ℕ → Ω → ℝ≥0∞) :
    ∀ k ω,
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞))
        (S k ω)).toNNReal ≤ (n : ℝ≥0) := by
  intro k ω
  have hext :=
    (avram_sweep16_original_double_min_clock_literal_extended_bounds
      X x D n S k ω).2.2
  exact_mod_cast hext
