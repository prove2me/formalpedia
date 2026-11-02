-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_gridfree_original_past_marked_rectangle_first_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:03:12.653355+00:00
-- url     : https://prove2.me/submissions/3ce5c2e1-1a73-4007-a7e9-c7cb72bc0b7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_past_restricted_marked_rectangle_lintegral_finite
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
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (s : ℝ≥0) (hst : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) ∂P) < ⊤ := by
  obtain ⟨grid, hGrid, hMesh, hBound⟩ :=
    avram_wave6_01_positive_horizon_fine_source_grid_witness T hT
  exact avram_wave6_01_bv_original_past_restricted_marked_rectangle_lintegral_finite
    X hBV hFinite T hT grid hGrid hMesh hBound s hst A hA B hB
