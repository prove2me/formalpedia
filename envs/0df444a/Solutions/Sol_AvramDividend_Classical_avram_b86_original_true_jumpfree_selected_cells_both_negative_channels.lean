-- Prove2me | solution 1 for AvramDividend.Classical.avram_b86_original_true_jumpfree_selected_cells_both_negative_channels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:08:59.969324+00:00
-- url     : https://prove2.me/submissions/ff8b2646-24de-4a1e-8a9b-897dd4c55c85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
import Theorems.Thm_AvramDividend_Classical_avram_b81_original_jumpfree_cell_large_mark_sum_constant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Both original negative source channels have their exact physical compensation and no-large-jump identities on unmarked stopped mesh cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) (J : Ω → Finset ℕ)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      ∀ u : ℝ≥0, s i ω < u → u ≤ t i ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ ω i, i ∈ S → i ∉ J ω →
      (Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
          ((t i ω : ℝ) - (s i ω : ℝ))) ∧
      (avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
       avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω)  := by
  intro ω i hi hNot
  let d : ℝ := -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
  have hMoment : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 d) :=
    (avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite).neg
  have hCut (n : ℕ) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t i ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s i ω) ω =
      ((t i ω : ℝ) - (s i ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by
    have h := avram_b80_original_jumpfree_cell_smallband_compensator_increment
      X n (s i ω) (t i ω) (hOrdered ω i hi) ω
      (hNoJump ω i hi hNot)
    rw [h]
    ring
  have hL : Tendsto (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t i ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s i ω) ω)
      atTop (𝓝 (Jsmall (t i ω) ω - Jsmall (s i ω) ω)) :=
    (hJlim ω (t i ω)).sub (hJlim ω (s i ω))
  have hR : Tendsto (fun n : ℕ =>
      ((t i ω : ℝ) - (s i ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)))
      atTop (𝓝 (((t i ω : ℝ) - (s i ω : ℝ)) * d)) :=
    tendsto_const_nhds.mul hMoment
  have hSeq : (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t i ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s i ω) ω) =
      (fun n : ℕ => ((t i ω : ℝ) - (s i ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))) := by
    funext n
    exact hCut n
  rw [hSeq] at hL
  have hEq := tendsto_nhds_unique hL hR
  constructor
  · simpa only [d] using hEq.trans (mul_comm _ _)
  · exact avram_b81_original_jumpfree_cell_large_mark_sum_constant
      X (s i ω) (t i ω) (hOrdered ω i hi) ω
      (hNoJump ω i hi hNot)
