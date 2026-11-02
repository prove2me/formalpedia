-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_gridfree_zero_activity_original_predictable_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:03:15.583446+00:00
-- url     : https://prove2.me/submissions/d71b0fd3-ef56-4377-9c1a-18cc8982eae5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_zero_negative_intensity_original_rectangle_compensator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hZero : X.ν (Iio (0 : ℝ)) = 0)
    (T : ℝ≥0) (hT : 0 < T)
    (s : ℝ≥0) (hst : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) =
      P A * ((T - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  obtain ⟨grid, hGrid, hMesh, hBound⟩ :=
    avram_wave6_01_positive_horizon_fine_source_grid_witness T hT
  exact avram_wave6_01_bv_zero_negative_intensity_original_rectangle_compensator
    X hBV hZero T hT grid hGrid hMesh hBound s hst A hA B hB
