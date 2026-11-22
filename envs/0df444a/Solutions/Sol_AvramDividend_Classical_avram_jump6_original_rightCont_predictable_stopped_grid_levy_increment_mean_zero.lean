-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_rightCont_predictable_stopped_grid_levy_increment_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:38:10.960178+00:00
-- url     : https://prove2.me/submissions/34575204-f196-4f24-b7e9-418e97684890

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Predictable centring of the genuine original Lévy first-order cell on
the right-continuous filtration. This is the filtration in which the
positive stopping-clock event is initially measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ) (κ : Ω → ℕ)
    (hWPast : Measurable[(𝓕.rightCont) (grid i)]
      (fun ω => if i < κ ω then H i ω else 0))
    (hWI : Integrable
      (fun ω => if i < κ ω then H i ω else 0) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P) :
    (∫ ω, (if i < κ ω then H i ω else 0) *
      (X.X (grid (i + 1)) ω - X.X (grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by
  obtain ⟨Y, hYX, hYc, hYσ, hYν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hYXI :
      Integrable (Y.X (grid (i + 1) - grid i)) P := by
    simpa only [hYX] using hXI
  have h :=
    avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
      Y grid i hGrid H κ hWPast hWI hYXI
  simpa only [hYX] using h

