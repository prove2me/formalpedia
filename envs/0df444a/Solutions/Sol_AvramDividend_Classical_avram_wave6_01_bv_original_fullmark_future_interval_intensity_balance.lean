-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_fullmark_future_interval_intensity_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:34:21.056968+00:00
-- url     : https://prove2.me/submissions/570f562d-2d05-4e81-9eae-183e3ae6d877

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_time_additive
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
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
    (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) +
      (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) =
    (t : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hAdd :=
    avram_wave6_01_original_past_marked_expected_count_time_additive
      X 0 s t (show (0 : ℝ≥0) ≤ s from zero_le) hst (Set.univ : Set Ω) (by simp)
        (Set.univ : Set ℝ) MeasurableSet.univ
  have hSourceAdd :
      (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc 0 t ×ˢ (Set.univ : Set ℝ)) ∂P) =
      (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc 0 s ×ˢ (Set.univ : Set ℝ)) ∂P) +
      (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) := by
    simpa using hAdd
  have hS :=
    avram_wave6_01_bv_original_total_jump_intensity_gridfree
      X hBV hFinite s hs
  have hT :=
    avram_wave6_01_bv_original_total_jump_intensity_gridfree
      X hBV hFinite t ht
  rw [hS, hT] at hSourceAdd
  exact hSourceAdd.symm
