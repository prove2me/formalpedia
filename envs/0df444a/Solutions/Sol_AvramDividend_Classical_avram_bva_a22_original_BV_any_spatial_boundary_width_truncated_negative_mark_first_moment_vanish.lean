-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:50:52.593823+00:00
-- url     : https://prove2.me/submissions/2accb689-7677-4b21-b35b-b54b8fe38ab1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun n => ∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν)
      atTop (𝓝 (0 : ℝ)) := by
  have hI : Integrable (fun z : ℝ => min (1 : ℝ) (-z))
      (X.ν.restrict (Iio (0 : ℝ))) :=
    avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
      X hBV 1 (by norm_num) (by norm_num)
  have hAe : ∀ᵐ z ∂X.ν.restrict (Iio (0 : ℝ)), z < 0 :=
    ae_restrict_mem measurableSet_Iio
  have hMeas (n : ℕ) :
      AEStronglyMeasurable (fun z : ℝ => min (ε n) (-z))
        (X.ν.restrict (Iio (0 : ℝ))) :=
    (avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
      X hBV (ε n) (hε n).1 (hε n).2).aestronglyMeasurable
  have hDom (n : ℕ) : ∀ᵐ z ∂X.ν.restrict (Iio (0 : ℝ)),
      ‖min (ε n) (-z)‖ ≤ ‖min (1 : ℝ) (-z)‖ := by
    filter_upwards [hAe] with z hz
    have hzn : (0 : ℝ) ≤ -z := le_of_lt (neg_pos.mpr hz)
    have hsmall : 0 ≤ min (ε n) (-z) :=
      le_min (le_of_lt (hε n).1) hzn
    have hbig : 0 ≤ min (1 : ℝ) (-z) :=
      le_min (by norm_num) hzn
    have hle : min (ε n) (-z) ≤ min (1 : ℝ) (-z) :=
      le_min ((min_le_left _ _).trans (hε n).2) (min_le_right _ _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hsmall, abs_of_nonneg hbig] using hle
  have hLimit : ∀ᵐ z ∂X.ν.restrict (Iio (0 : ℝ)),
      Tendsto (fun n => min (ε n) (-z)) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAe] with z hz
    have hT : Tendsto (fun n => min (ε n) (-z))
        atTop (𝓝 (min (0 : ℝ) (-z))) :=
      hεlim.min tendsto_const_nhds
    have hzero : min (0 : ℝ) (-z) = 0 :=
      min_eq_left (le_of_lt (neg_pos.mpr hz))
    simpa only [hzero] using hT
  have hConv :=
    tendsto_integral_of_dominated_convergence
      (fun z : ℝ => ‖min (1 : ℝ) (-z)‖)
      hMeas hI.norm hDom hLimit
  simpa using hConv
