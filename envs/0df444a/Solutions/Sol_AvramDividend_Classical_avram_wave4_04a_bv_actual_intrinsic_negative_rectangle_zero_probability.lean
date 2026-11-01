-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_rectangle_zero_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:24:01.447977+00:00
-- url     : https://prove2.me/submissions/9ab5b54b-4b02-4bbc-a037-5976486b4458

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_source_jumps_interval_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Zero-count Poisson law of the true original-source negative jump measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} =
      Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal)) := by
  have hEvents :
      {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} =
      {ω : Ω |
        ∀ u : ℝ≥0, u ∈ Ioc s t →
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} := by
    ext ω
    exact
      avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
        X ω s t
  rw [hEvents]
  exact
    avram_wave4_04a_bv_actual_no_source_jumps_interval_probability
      X hBV hFinite s t hst
