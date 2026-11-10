-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_residual_limit_unique_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:03:03.892675+00:00
-- url     : https://prove2.me/submissions/9803901a-bea6-49cb-a7a5-59d0b431a475

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae

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
      (∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
                R T ω| ≤ η)) ∧
      (∀ S : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (S T ω))) →
        ∀ᵐ ω ∂P, ∀ T : ℝ≥0, S T ω = R T ω) := by
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  refine ⟨R, hR, ?_⟩
  intro S hS
  filter_upwards [hR, hS] with ω hRω hSω
  intro T
  exact tendsto_nhds_unique (hSω T) (hRω.1 T)
