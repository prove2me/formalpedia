-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:33:27.708469+00:00
-- url     : https://prove2.me/submissions/7d45e72d-d82f-4791-8869-02779f8307c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_actual_negative_predictable_rectangle
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_horizon_predictable_rectangle
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_mark_negative_support_count
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Finite-activity BV original predictable negative-mark compensation,
including the time-zero left endpoint and the degenerate interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  classical
  by_cases hs0 : s = 0
  · subst s
    by_cases ht : t = 0
    · subst t
      exact avram_wave7_01_original_zero_horizon_predictable_rectangle
        X 0 A hA (Iio (0 : ℝ)) measurableSet_Iio
    · have htpos : (0 : ℝ≥0) < t :=
        lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm ht)
      have hSource :
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ)) ∂P) =
          (t : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
        calc
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ)) ∂P) =
              (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ (Set.univ : Set ℝ)) ∂P) := by
            apply lintegral_congr
            intro ω
            have h := avram_wave7_01_original_arbitrary_mark_negative_support_count
              X ω 0 t hst (Set.univ : Set ℝ) MeasurableSet.univ
            simpa only [Set.univ_inter] using h.symm
          _ = _ := avram_wave6_01_bv_original_total_jump_intensity_gridfree
            X hBV hFinite t htpos
      have hFactor :=
        avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
          X 0 t hst A hA (Iio (0 : ℝ)) measurableSet_Iio
      calc
        (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ)) ∂P) =
            P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ)) ∂P) := hFactor
        _ = P A * ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) := by rw [hSource]
        _ = P A * ((t - (0 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
          simp only [tsub_zero, mul_assoc]
  · have hspos : (0 : ℝ≥0) < s :=
        lt_of_le_of_ne (show (0 : ℝ≥0) ≤ s from zero_le) (Ne.symm hs0)
    exact avram_wave7_01_bv_finite_activity_actual_negative_predictable_rectangle
      X hBV hFinite s t hspos hst A hA
