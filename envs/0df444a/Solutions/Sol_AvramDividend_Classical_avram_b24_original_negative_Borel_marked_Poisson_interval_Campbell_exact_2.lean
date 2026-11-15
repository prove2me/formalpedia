-- Prove2me | solution 2 for AvramDividend.Classical.avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:47:22.448759+00:00
-- url     : https://prove2.me/submissions/f9f07f0d-bdc9-4ef8-b317-2784c62c4a88

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B  := by
  have ht : s + (t - s) = t := add_tsub_cancel_of_le hst
  have hSource :=
    (avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
      X s (t - s) B hB).trans
      (avram_ja34_original_all_negative_borel_expected_count_exact
        X (t - s) B hB hNeg)
  simpa only [ht] using hSource
