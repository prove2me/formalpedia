-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_BV_physical_jumpmarks_compensation_equals_drift_adjustment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:50.488259+00:00
-- url     : https://prove2.me/submissions/0b0cc23e-78ef-4d68-9f73-cc016615cbb8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical BV source compensation follows from raw marked jump convergence and exact drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        Jsmall t ω =
      (t : ℝ) * (X.drift - X.c) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  have hRaw :=
    avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
      X hFinite
  have hNu :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  have hDrift :=
    avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator X
  filter_upwards [hRaw, hJ] with ω hRawω hJω
  intro t
  have hNuT : Tendsto
      (fun n : ℕ => (t : ℝ) *
        (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop
      (𝓝 ((t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    tendsto_const_nhds.mul hNu
  have hCompT : Tendsto (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
        (t : ℝ) *
          (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 (avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        Jsmall t ω + (t : ℝ) *
        (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    (tendsto_const_nhds.add (hJω t)).add hNuT
  have hEq := tendsto_nhds_unique hCompT (hRawω t)
  have hShift : (t : ℝ) * (X.drift - X.c) =
      -(t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by
    rw [hDrift]
    ring
  nlinarith [hEq, hShift]
