-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_total_jump_intensity_gridfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:03:25.876306+00:00
-- url     : https://prove2.me/submissions/e79474b9-e012-49fe-9bd1-bf21d083b75d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
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
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  obtain ⟨grid, hGrid, hMesh, hBound⟩ :=
    avram_wave6_01_positive_horizon_fine_source_grid_witness T hT
  exact avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
    X hBV hFinite T hT grid hGrid hMesh hBound
