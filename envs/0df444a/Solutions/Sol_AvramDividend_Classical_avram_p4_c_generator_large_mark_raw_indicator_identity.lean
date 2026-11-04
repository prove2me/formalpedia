-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_large_mark_raw_indicator_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:34:36.166162+00:00
-- url     : https://prove2.me/submissions/86c889a4-ed7b-4f81-8962-90d750ac2d7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (w : ℝ → ℝ) (y z ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hz : z ∈ Iio (-ε)) :
    w (y + z) - w y =
      SpectrallyNegativeLevy.generatorIntegrand w y z +
      deriv w y * (Ioo (-1 : ℝ) (-ε)).indicator (fun t : ℝ => t) z := by
  change z < -ε at hz
  by_cases hz1 : z ≤ -1
  · have hnotBand : z ∉ Ioo (-1 : ℝ) (-ε) := by
      intro hb
      exact (not_lt_of_ge hz1) hb.1
    have hnotSource : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hs
      exact (not_lt_of_ge hz1) hs.1
    simp [SpectrallyNegativeLevy.generatorIntegrand,
      Set.indicator_of_notMem hnotBand, Set.indicator_of_notMem hnotSource]
  · have hband : z ∈ Ioo (-1 : ℝ) (-ε) :=
      ⟨lt_of_not_ge hz1, hz⟩
    have hsource : z ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · exact hband.1
      · linarith [hband.2, hε]
    simp [SpectrallyNegativeLevy.generatorIntegrand,
      Set.indicator_of_mem hband, Set.indicator_of_mem hsource] <;> ring
