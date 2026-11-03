-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_two_cell_L2_isometry_of_centered_future_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:35:20.498455+00:00
-- url     : https://prove2.me/submissions/952ea798-cc30-43c3-9db3-8d1925036157

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_two_cell_L2_additivity_from_orthogonality
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_centered_increment_cross_moment_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original-source finite two-cell L² isometry under centring and integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P)
    (hSqA : Integrable (fun ω => (X.X (s + u) ω - X.X s ω)^2) P)
    (hSqB : Integrable (fun ω =>
      (X.X (s + u + v) ω - X.X (s + u) ω)^2) P)
    (hAB : Integrable (fun ω =>
      (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω)) P)
    (hMeanFirst : (∫ ω, X.X (s + u) ω - X.X s ω ∂P) = 0)
    (hMeanSecond :
      (∫ ω, X.X (s + u + v) ω - X.X (s + u) ω ∂P) = 0) :
    (∫ ω, (X.X (s + u + v) ω - X.X s ω)^2 ∂P) =
      (∫ ω, (X.X (s + u) ω - X.X s ω)^2 ∂P) +
      (∫ ω, (X.X (s + u + v) ω - X.X (s + u) ω)^2 ∂P) := by
  exact avram_wave7_06_original_two_cell_L2_additivity_from_orthogonality
    X s u v hSqA hSqB hAB
    (avram_wave7_06_original_consecutive_centered_increment_cross_moment_zero
      X s u v hFirst hSecond hMeanFirst hMeanSecond)
