-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_random_horizon_strict_reversal_no_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:44:08.54086+00:00
-- url     : https://prove2.me/submissions/7454930f-5221-4393-91fd-2c904eee3ecc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_random_horizon_strict_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Q : Measure Θ) [SFinite Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (a : ℝ) :
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a} =
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a} := by
  obtain ⟨hL, hR⟩ :=
    avram_ws01e_b_levy_random_horizon_strict_events_measurable
      X e he a
  exact avram_ws01e_b_independent_random_horizon_strict_reversal
    X Q e he a hL hR
