-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:54:07.66949+00:00
-- url     : https://prove2.me/submissions/fe27ad1b-9337-45e4-9e9f-3f9b6b7ee5ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_future_interval_intensity_balance
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
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  have hBalance :=
    avram_wave6_01_bv_original_fullmark_future_interval_intensity_balance
      X hBV hFinite s t hs hst
  have hTime : s + (t - s) = t := add_tsub_cancel_of_le hst
  have hTimeENN :
      (s : ℝ≥0∞) + ((t - s : ℝ≥0) : ℝ≥0∞) = (t : ℝ≥0∞) := by
    exact_mod_cast hTime
  have hRate :
      (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) +
          ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) =
        (t : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    rw [← add_mul, hTimeENN]
  have hFiniteStart :
      (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top (by simp) hFinite)
  have hCancel :
      (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) +
          (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) +
          (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    calc
      _ = (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) +
          (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
            (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) := by ac_rfl
      _ = (t : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := hBalance
      _ = (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) +
          ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := hRate.symm
      _ = _ := by ac_rfl
  exact (ENNReal.add_left_inj hFiniteStart).mp hCancel
