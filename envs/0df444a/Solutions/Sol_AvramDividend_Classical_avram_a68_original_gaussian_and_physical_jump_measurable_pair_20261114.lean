-- Prove2me | solution 1 for AvramDividend.Classical.avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:56:23.080456+00:00
-- url     : https://prove2.me/submissions/020a7e58-c850-437a-9b6d-826e6b55874e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
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
        atTop (𝓝 (R t ω))) (t : ℝ≥0) :
    ∃ H J : Ω → ℝ,
      Measurable H ∧ Measurable J ∧
      (H =ᵐ[P] R t) ∧
      (J =ᵐ[P] fun ω =>
        ∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0) ∧
      (∀ ω, H ω + J ω =
        X.X t ω -
          (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by
  obtain ⟨G, hAdapt, _, hEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  let H : Ω → ℝ := G t
  let J : Ω → ℝ := fun ω =>
    X.X t ω - (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) - H ω
  have hHMeas : Measurable H :=
    (hAdapt t).mono (𝓕.le t) le_rfl
  have hXMeas : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hJMeas : Measurable J :=
    (hXMeas.sub measurable_const).sub hHMeas
  refine ⟨H, J, hHMeas, hJMeas, ?_, ?_, ?_⟩
  · filter_upwards [hEq] with ω hω
    exact hω t
  · have hSource :=
      avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
        X hFinite R hR
    filter_upwards [hEq, hSource] with ω hω hSω
    dsimp [J, H]
    rw [hω t]
    have hIdentity := hSω t
    linarith
  · intro ω
    dsimp [H, J]
    ring
