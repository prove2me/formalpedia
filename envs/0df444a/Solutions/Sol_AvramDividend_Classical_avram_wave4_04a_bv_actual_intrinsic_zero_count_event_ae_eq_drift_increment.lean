-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_zero_count_event_ae_eq_drift_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:15:57.786782+00:00
-- url     : https://prove2.me/submissions/b4d3095d-4d9b-4a51-96ca-9805e9e3c32f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original marked count-zero event is a.e. an adapted drift increment event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} =ᵐ[P]
    {ω : Ω | X.X t ω - X.X s ω =
      ((t : ℝ) - (s : ℝ)) * X.drift} := by
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
    exact avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
      X ω s t
  change N0 =ᵐ[P] {ω : Ω | X.X t ω - X.X s ω =
    ((t : ℝ) - (s : ℝ)) * X.drift}
  rw [hEvents]
  exact avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
    X hBV hFinite s t hst
