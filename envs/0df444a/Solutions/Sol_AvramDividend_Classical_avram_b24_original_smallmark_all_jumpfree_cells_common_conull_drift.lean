-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:56:17.945418+00:00
-- url     : https://prove2.me/submissions/ca50f1d9-9fb7-423d-96fd-7591bfeb6fb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
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
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω))) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (∀ u : ℝ≥0, s < u → u ≤ t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      Jsmall t ω - Jsmall s ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) * ((t : ℝ) - (s : ℝ)) := by
  have hMoment :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  have hNeg : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    hMoment.neg
  filter_upwards [hJsource] with ω hLimω
  intro s t hOrder hNoω
  have hCut (k : ℕ) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k s ω =
      ((t : ℝ) - (s : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν)) := by
    have h :=
      avram_b80_original_jumpfree_cell_smallband_compensator_increment
        X k s t hOrder ω hNoω
    rw [h]
    ring
  have hSourceLimit : Tendsto (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k s ω)
      atTop (𝓝 (Jsmall t ω - Jsmall s ω)) :=
    (hLimω t).sub (hLimω s)
  have hLimitMoment : Tendsto (fun k : ℕ =>
      ((t : ℝ) - (s : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν)))
      atTop (𝓝 (((t : ℝ) - (s : ℝ)) *
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)))) :=
    tendsto_const_nhds.mul hNeg
  have hSeq : (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k s ω) =
      (fun k : ℕ => ((t : ℝ) - (s : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν))) := by
    funext k
    exact hCut k
  rw [hSeq] at hSourceLimit
  have hEq := tendsto_nhds_unique hSourceLimit hLimitMoment
  nlinarith
