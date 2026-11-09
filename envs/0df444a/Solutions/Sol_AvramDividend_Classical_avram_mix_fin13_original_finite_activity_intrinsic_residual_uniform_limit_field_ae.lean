-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:26:42.343802+00:00
-- url     : https://prove2.me/submissions/06070814-79dc-46b2-b69c-b1e89eda0bb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_limit_uniform_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      ∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
                R T ω| ≤ η) := by
  obtain ⟨G, hG⟩ :=
    avram_ubv_mixed13_original_finite_activity_physical_residual_limit_uniform_ae
      X hFinite
  let R : ℝ≥0 → Ω → ℝ := fun t ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω - G t ω
  refine ⟨R, ?_⟩
  filter_upwards [hG] with ω hω
  rcases hω with ⟨hPoint, hUniform⟩
  have hIdentity (t : ℝ≥0) (n : ℕ) :
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
    unfold avram_p4_h_gaussian_intrinsic_truncated_residual
    ring
  constructor
  · intro t
    have hlim :
        Tendsto (fun n : ℕ =>
          (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
            avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
          atTop (nhds
            ((avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
              avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
              G t ω)) := by
      exact tendsto_const_nhds.sub (hPoint t)
    change Tendsto
      (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
      atTop (nhds
        ((avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
          G t ω))
    have hEq : (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) =
      (fun n : ℕ =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by
      funext n
      exact hIdentity t n
    rw [hEq]
    exact hlim
  · intro K η hη
    obtain ⟨N, hN⟩ := hUniform K η hη
    refine ⟨N, ?_⟩
    intro n hn t ht
    change |avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
      ((avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
        G t ω)| ≤ η
    have hEq :
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          ((avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
              avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
            G t ω) =
          -(avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            G t ω) := by
      rw [hIdentity t n]
      ring
    rw [hEq, abs_neg]
    exact hN n hn t ht
