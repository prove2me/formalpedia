-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_original_zero_start_negative_mark_exact_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:39:17.795568+00:00
-- url     : https://prove2.me/submissions/679c7d94-0072-4801-9818-d035644423e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_mark_negative_support_count

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Time-zero finite-activity original negative-mark first-moment identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) ∂P) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hPoint (ω : Ω) :
      N ω (Ioc 0 T ×ˢ Iio (0 : ℝ)) =
        N ω (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) := by
    have hRestrict :=
      avram_wave7_01_original_arbitrary_mark_negative_support_count
        X ω 0 T (by positivity) Set.univ MeasurableSet.univ
    simpa only [Set.univ_inter] using hRestrict.symm
  change (∫⁻ ω, N ω (Ioc 0 T ×ˢ Iio (0 : ℝ)) ∂P) =
    (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))
  calc
    (∫⁻ ω, N ω (Ioc 0 T ×ˢ Iio (0 : ℝ)) ∂P) =
      ∫⁻ ω, N ω (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P := by
        apply lintegral_congr
        intro ω
        exact hPoint ω
    _ = _ := avram_wave6_01_bv_original_total_jump_intensity_gridfree
      X hBV hFinite T hT
