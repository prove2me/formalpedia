-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_signed_tests_determine_negative_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:06:08.348214+00:00
-- url     : https://prove2.me/submissions/cb6932f4-f4f8-44aa-a1f4-41ec31e3f569

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_signed_tests_negative_borel_of_transport
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_subtype_comap_integral_from_real_test
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- Actual subtype comap transport discharges the generic signed-test Borel uniqueness interface. -/
theorem solution
    (μ ν : Measure ℝ)
    (hμBand : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hνBand : ∀ δ : ℝ, 0 < δ → ν (Iic (-δ)) < ⊤)
    (hSigned : ∀ (g : ℝ → ℝ), Continuous g →
      IsCompact (tsupport g) → tsupport g ⊆ Iio (0 : ℝ) →
      (∫ y, g y ∂μ) = (∫ y, g y ∂ν))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    μ B = ν B := by
  exact avram_p2_a_assist_signed_tests_negative_borel_of_transport
    μ ν hμBand hνBand hSigned
    (fun f g hneg hagree =>
      avram_p2_a_assist_subtype_comap_integral_from_real_test
        μ f g hneg hagree)
    (fun f g hneg hagree =>
      avram_p2_a_assist_subtype_comap_integral_from_real_test
        ν f g hneg hagree)
    B hB ε hε hBsep
