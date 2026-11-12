-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja22_original_tail_variance_from_finite_strip_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:24:34.242073+00:00
-- url     : https://prove2.me/submissions/4e750a42-b44c-4bae-ad8b-2431cd73b823

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja24_original_levy_quadratic_strip_energy_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ja24_original_gaussian_cutoff_difference_square_expectation_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical L2 limit and deterministic Levy strip limit identify the tail energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))
    (hStrip : ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      Integrable (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc
          (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        R t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioo
          (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  let A : ℕ → ℝ := fun m =>
    ∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P
  let B : ℕ → ℝ := fun m =>
    ∫ z in Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))),
      z ^ 2 ∂X.ν
  let F : ℝ :=
    ∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
      R t ω) ^ 2 ∂P
  let G : ℝ :=
    ∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν
  obtain ⟨hInt, hA⟩ :=
    avram_ja24_original_gaussian_cutoff_difference_square_expectation_tendsto
      X hX hFinite R hR hStrip n t
  have hB := avram_ja24_original_levy_quadratic_strip_energy_tendsto
    X hFinite n
  change Tendsto A atTop (nhds F) at hA
  change Tendsto B atTop (nhds G) at hB
  have hEq : ∀ᶠ m in atTop, A m = (t : ℝ) * B m := by
    filter_upwards [eventually_ge_atTop n] with m hnm
    exact (hStrip n m hnm t).2
  have hEqSymm : ∀ᶠ m in atTop,
      (t : ℝ) * B m = A m := by
    filter_upwards [hEq] with m hm
    exact hm.symm
  have hMul : Tendsto (fun m => (t : ℝ) * B m)
      atTop (nhds ((t : ℝ) * G)) :=
    tendsto_const_nhds.mul hB
  have hA' : Tendsto A atTop (nhds ((t : ℝ) * G)) :=
    hMul.congr' hEqSymm
  have hLimit : F = (t : ℝ) * G :=
    tendsto_nhds_unique hA hA'
  exact ⟨hInt, hLimit⟩
