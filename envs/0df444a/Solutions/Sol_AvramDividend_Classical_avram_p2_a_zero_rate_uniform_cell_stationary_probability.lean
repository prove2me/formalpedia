-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_stationary_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:50:02.846397+00:00
-- url     : https://prove2.me/submissions/31e317dd-2ce9-47ee-ab68-74b47c681433

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_width

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Each original source-grid cell has the same original-process
one-time mark probability because its NNReal width is δ. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (j : ℕ) (δ : ℝ≥0) (B : Set ℝ) :
    P {ω : Ω | X.X (((((j + 1 : ℕ) : ℝ≥0) * δ) - ((j : ℝ≥0) * δ))) ω ∈ B} =
    P {ω : Ω | X.X δ ω ∈ B} := by
  rw [avram_p2_a_zero_rate_uniform_cell_width]
