-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb48_original_zero_negative_mark_kernel_eq_intensity_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:50:54.146572+00:00
-- url     : https://prove2.me/submissions/436c715f-cb3b-42c3-bdcb-c7d132278692

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_negative_mark_kernel_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) =
      -(w 0) * (X.ν (Iio (0 : ℝ))).toReal := by
  exact avram_bvb22_original_zero_contact_negative_mark_kernel_exact
    X w (fun z hz => hwNeg z hz) hActivity
