-- Prove2me | solution 1 for AvramDividend.Classical.avram_a35_original_intrinsic_gaussian_equals_drift_adjusted_physical_jumpfree_source_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:11:21.006211+00:00
-- url     : https://prove2.me/submissions/5ae134ed-0d3a-4674-9bab-e19d6532d6f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
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
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω =
        X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0) := by
  have hMark :=
    avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
      X hFinite
  have hComp :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  filter_upwards [hR, hMark] with ω hRω hMarkω
  intro t
  let I : ℕ → ℝ := fun n =>
    ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν
  let Iall : ℝ := ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν
  let J : ℝ := ∑' u : ℝ≥0,
    if 0 < u ∧ u ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
    else 0
  have hAdd :=
    (hRω t).add (hMarkω t)
  have hAlgebra (n : ℕ) :
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω +
        (avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
          (t : ℝ) * I n) =
        X.X t ω - (t : ℝ) * X.c + (t : ℝ) * I n := by
    dsimp [avram_p4_h_gaussian_intrinsic_truncated_residual]
    ring
  have hSeq : Tendsto
      (fun n : ℕ => X.X t ω - (t : ℝ) * X.c + (t : ℝ) * I n)
      atTop (𝓝 (R t ω - J)) := by
    convert hAdd using 1
    · funext n
      exact (hAlgebra n).symm
    · dsimp [J]
      ring
  have hI : Tendsto I atTop (𝓝 Iall) := hComp
  have hExpected : Tendsto
      (fun n : ℕ => X.X t ω - (t : ℝ) * X.c + (t : ℝ) * I n)
      atTop (𝓝 (X.X t ω - (t : ℝ) * X.c + (t : ℝ) * Iall)) := by
    exact (tendsto_const_nhds.sub tendsto_const_nhds).add
      (hI.const_mul (t : ℝ))
  have hUnique : R t ω - J =
      X.X t ω - (t : ℝ) * X.c + (t : ℝ) * Iall :=
    tendsto_nhds_unique hSeq hExpected
  dsimp [Iall, J] at hUnique ⊢
  linarith
