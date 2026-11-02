-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:39:21.327317+00:00
-- url     : https://prove2.me/submissions/45c67fca-0e7a-441a-b561-40787e3cc593

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  by_cases hs0 : s = 0
  · subst s
    by_cases ht0 : t = 0
    · subst t
      simp
    · have htpos : 0 < t := pos_iff_ne_zero.mpr ht0
      simpa using
        (avram_wave6_01_bv_original_total_jump_intensity_gridfree
          X hBV hFinite t htpos)
  · have hspos : 0 < s := pos_iff_ne_zero.mpr hs0
    exact avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
      X hBV hFinite s t hspos hst
