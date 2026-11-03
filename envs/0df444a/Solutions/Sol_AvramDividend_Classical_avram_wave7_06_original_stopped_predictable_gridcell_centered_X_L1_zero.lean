-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:11:32.557292+00:00
-- url     : https://prove2.me/submissions/e909ad75-59f4-4d2b-8391-88e4bf8c4495

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original source stopped predictable step weight has zero expected product
with its original centred future grid-cell X increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : Measurable[𝓕 (grid i)]
      (fun ω => if i < τ ω then H i ω else 0))
    (hWI : Integrable (fun ω =>
      if i < τ ω then H i ω else 0) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P) :
    (∫ ω, (if i < τ ω then H i ω else 0) *
      (X.X (grid (i + 1)) ω - X.X (grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by
  have hZero :=
    avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
      X (grid i) (grid (i + 1) - grid i)
      (fun ω => if i < τ ω then H i ω else 0)
      hWPast hWI hXI
  simpa only [add_tsub_cancel_of_le hGrid] using hZero
