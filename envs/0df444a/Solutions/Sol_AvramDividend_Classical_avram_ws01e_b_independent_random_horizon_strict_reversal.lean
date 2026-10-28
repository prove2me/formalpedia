-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_independent_random_horizon_strict_reversal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:17:05.953016+00:00
-- url     : https://prove2.me/submissions/b9b3bed9-e94b-452d-a501-9e4c837d5e81

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_clock_section_probability_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_horizon_strict_reversal

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Q : Measure Θ) [SFinite Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (a : ℝ)
    (hL : MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a})
    (hR : MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a}) :
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X (e z.2) z.1 - X.X s z.1 < a} =
    (P.prod Q) {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧
        X.X s z.1 - X.X 0 z.1 < a} := by
  refine avram_ws01e_b_independent_clock_section_probability_transfer P Q _ _ hL hR (fun η => ?_)
  rcases eq_zero_or_pos (e η) with h | h
  · congr 1
    ext ω
    simp [h]
  · exact avram_ws01e_b_fixed_horizon_strict_reversal X (e η) h a
