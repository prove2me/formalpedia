-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_smallband_mark_path_from_finite_jump_cutoff_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:56:31.781205+00:00
-- url     : https://prove2.me/submissions/90f3b48d-b9c2-412d-93a3-dc54d7da0689

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (ω : Ω) (t : ℝ≥0) (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : Tendsto (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
      atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hCut : Tendsto (fun n : ℕ =>
      ∑ u ∈ S, if -1 < X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))
      then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0)
      atTop (𝓝 (∑ u ∈ S,
        if -1 < X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
           X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0))) :
    Jsmall t ω =
      (∑ u ∈ S,
        if -1 < X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
           X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0) -
      (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by
  have hMoment :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  have hComp : Tendsto (fun n : ℕ => (t : ℝ) *
      (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 ((t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    tendsto_const_nhds.mul hMoment
  have hLimit : Tendsto (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
      (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
        (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 (Jsmall t ω +
        (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    hJsource.add hComp
  have hEq (n : ℕ) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
      (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
        (-(1 / ((n : ℝ) + 1))), z ∂X.ν) =
      ∑ u ∈ S, if -1 < X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))
      then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0 :=
    avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
      X ω t n S hS
  have hFn : (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
      (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
        (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) =
      (fun n : ℕ => ∑ u ∈ S, if -1 < X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0) := by
    funext n
    exact hEq n
  rw [hFn] at hLimit
  have hUnique := tendsto_nhds_unique hLimit hCut
  linarith
