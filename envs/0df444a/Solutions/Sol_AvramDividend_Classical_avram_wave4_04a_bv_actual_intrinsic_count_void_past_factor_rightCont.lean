-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_void_past_factor_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:29:25.272501+00:00
-- url     : https://prove2.me/submissions/842a6c5f-ed9e-4825-8940-1152def8bec5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_nojump_past_factor_rightCont

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original source marked-count void event factors from its original past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕.rightCont s) A) :
    P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0}) =
      P A * P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} := by
  let N0 : Set Ω := {ω : Ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) = 0}
  let J0 : Set Ω := {ω : Ω | ∀ u : ℝ≥0, u ∈ Ioc s t →
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0}
  have hEvents : N0 = J0 := by
    ext ω
    exact
      avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
        X ω s t
  change P (A ∩ N0) = P A * P N0
  rw [hEvents]
  exact avram_wave4_04a_bv_actual_nojump_past_factor_rightCont
    X hBV hFinite s t hst A hA
