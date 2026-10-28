-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_finite_attained_times_strict
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:52:05.433826+00:00
-- url     : https://prove2.me/submissions/40ebb6fc-c25f-4a0f-ab94-2a696551dd8e

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_finite_attained_times_mono
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b c : ℝ) (hb : 0 ≤ b) (hbc : b < c)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞))) : (u : ℝ) < (v : ℝ) := by
  refine lt_of_le_of_ne (firstUpcrossing_finite_attained_times_mono X ω b c hbc.le u v hu hv) ?_
  intro h
  have h1 := firstUpcrossing_value_eq_threshold X b hb ω u hu
  have h2 := firstUpcrossing_value_eq_threshold X c (hb.trans hbc.le) ω v hv
  rw [NNReal.coe_inj.1 h] at h1
  linarith
