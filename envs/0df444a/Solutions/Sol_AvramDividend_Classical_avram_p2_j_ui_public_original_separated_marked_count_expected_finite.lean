-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_separated_marked_count_expected_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:27:57.907384+00:00
-- url     : https://prove2.me/submissions/cde5d81c-38ed-4113-94bc-d1de5f282da6

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original intrinsic marked-count expectation is finite on separated negative bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) < ⊤ := by
  obtain ⟨markRate, hRate, hFinite, _, _⟩ :=
    avram_p2_c_borel_original_intrinsic_intensity_measure_complete X
  have hBfinite : markRate B < ⊤ :=
    lt_of_le_of_lt (measure_mono hBsep) (hFinite ε hε)
  rw [hRate T B hB]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBfinite
