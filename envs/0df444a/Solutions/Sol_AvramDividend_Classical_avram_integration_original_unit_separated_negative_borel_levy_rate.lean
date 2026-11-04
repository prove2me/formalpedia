-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_original_unit_separated_negative_borel_levy_rate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:58:03.690149+00:00
-- url     : https://prove2.me/submissions/92ea8f07-8e3c-4d47-bb83-f43b94e4df35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_negative_halfline_threshold_rates

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-! Cutoff plus all lower-halfline source tests determine separated Borel marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B := by
  obtain ⟨hCut, hBelow⟩ :=
    avram_integration_original_unit_negative_halfline_threshold_rates X ε hε
  have hFinite : X.ν (Iic (-ε)) ≠ ⊤ :=
    (avram_p2_a_zero_rate_separated_borel_nu_finite
      X (Iic (-ε)) measurableSet_Iic ε hε (by rfl)).ne
  have hDense : Dense (Set.univ : Set ℝ) := dense_univ
  have hExt :=
    avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff
      X (0 : ℝ≥0) (1 : ℝ≥0) (by norm_num)
      ε hε X.ν hFinite Set.univ hDense
      hCut (fun a _ ha => hBelow a ha) B hB
  simpa only [Set.inter_eq_left.mpr hBsep] using hExt
