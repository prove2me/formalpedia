-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_original_any_start_negative_mark_exact_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:01:55.602514+00:00
-- url     : https://prove2.me/submissions/e33ce1a5-cfbd-42f9-9c3a-b870ee8a4995

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_zero_start_negative_mark_exact_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The BV finite-activity original negative-mark rate covers s = 0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  by_cases hs0 : s = 0
  · subst s
    by_cases ht0 : t = 0
    · subst t
      simp
    · have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht0
      simpa only [tsub_zero] using
        (avram_wave7_01_bv_original_zero_start_negative_mark_exact_rate
          X hBV hFinite t htpos)
  · have hspos : (0 : ℝ≥0) < s := pos_iff_ne_zero.mpr hs0
    exact avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
      X hBV hFinite s t hspos hst
