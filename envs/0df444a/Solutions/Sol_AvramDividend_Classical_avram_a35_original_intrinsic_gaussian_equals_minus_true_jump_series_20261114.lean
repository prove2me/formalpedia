-- Prove2me | solution 1 for AvramDividend.Classical.avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:13:05.035351+00:00
-- url     : https://prove2.me/submissions/97ae8531-d42e-4c8f-8b4b-2b0d0030c018

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a35_original_intrinsic_gaussian_equals_drift_adjusted_physical_jumpfree_source_20261114
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
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω =
        X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) -
        (∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            X.X u ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0) := by
  have hPhys :=
    avram_a35_original_intrinsic_gaussian_equals_drift_adjusted_physical_jumpfree_source_20261114
      X hFinite R hR
  filter_upwards [hPhys] with ω hω
  intro t
  have hTerm (u : ℝ≥0) :
      (if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
       else 0) =
      -(if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
       else 0) := by
    split_ifs <;> ring
  have hTsum :
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
       else 0) =
      -(∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
       else 0) := by
    rw [← tsum_neg]
    congr 1
    funext u
    exact hTerm u
  rw [hω t, hTsum]
  ring
