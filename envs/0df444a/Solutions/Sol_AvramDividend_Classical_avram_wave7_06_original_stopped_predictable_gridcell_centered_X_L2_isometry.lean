-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:01:07.777176+00:00
-- url     : https://prove2.me/submissions/4be52099-9cdb-4fb8-aac9-dbbb31f74829

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact source stopped predictable step-cell L² isometry, including its
original time-grid endpoints and source probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : Measurable[𝓕 (grid i)]
      (fun ω => if i < τ ω then H i ω else 0))
    (hW2 : Integrable (fun ω =>
      (if i < τ ω then H i ω else 0)^2) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P)
    (hXSq : Integrable (fun ω =>
      (X.X (grid (i + 1) - grid i) ω)^2) P) :
    (∫ ω,
      ((if i < τ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P)))^2 ∂P) =
    (∫ ω, (if i < τ ω then H i ω else 0)^2 ∂P) *
      (∫ ω, (X.X (grid (i + 1) - grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P))^2 ∂P) := by
  have hIso :=
    avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
      X (grid i) (grid (i + 1) - grid i)
      (fun ω => if i < τ ω then H i ω else 0)
      hWPast hW2 hXI hXSq
  simpa only [add_tsub_cancel_of_le hGrid] using hIso
