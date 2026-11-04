-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_clipped_NNReal_clocks_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:24:26.866501+00:00
-- url     : https://prove2.me/submissions/9270668c-a146-42dc-bd76-a81f15e63b7b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The exact source finite ruin-clipped NNReal clocks are pathwise increasing in the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω, Monotone (fun n : ℕ =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) := by
  intro ω m n hmn
  have hm :=
    (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D m).1 ω
  have hn :=
    (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).1 ω
  have hcast : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hmn
  have hmin : min (ruinTime X x D ω) (m : ℝ≥0∞) ≤
      min (ruinTime X x D ω) (n : ℝ≥0∞) :=
    min_le_min_left _ hcast
  have hcoe : (((min (ruinTime X x D ω) (m : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
      (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [hm, hn]
    exact hmin
  exact_mod_cast hcoe
