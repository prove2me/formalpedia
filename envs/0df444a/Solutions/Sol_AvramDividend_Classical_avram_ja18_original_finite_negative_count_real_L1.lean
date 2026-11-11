-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_finite_negative_count_real_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:24:54.931197+00:00
-- url     : https://prove2.me/submissions/cead5109-2a06-4986-b16d-b1a38f65c5ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The literal original negative jump count on a bounded integer horizon
is real integrable, directly from its genuine source-count lintegral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    Integrable (fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal) P := by
  apply integrable_toReal_of_lintegral_ne_top
    (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X 0 (n : ℝ≥0) (by positivity)
      (Iio (0 : ℝ)) measurableSet_Iio).aemeasurable
  have h := avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
    X hFinite n (fun _ => (n : ℝ≥0)) (by intro ω; exact le_rfl)
  exact ne_of_lt h
