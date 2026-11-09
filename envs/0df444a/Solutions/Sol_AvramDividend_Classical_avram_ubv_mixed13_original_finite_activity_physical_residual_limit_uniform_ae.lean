-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_limit_uniform_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:39:26.985544+00:00
-- url     : https://prove2.me/submissions/cb1ce83e-ba8d-47bd-bce4-b19e16e760bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_uniform_compact_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original finite-activity compensated cutoff source has one
sample-path limit, uniformly on every bounded physical time interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      ∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω)
            atTop (𝓝 (G T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
                G T ω| ≤ η) := by
  obtain ⟨G, hG⟩ :=
    avram_ubv_mixed13_original_finite_activity_physical_residual_limit_field_ae
      X hFinite
  refine ⟨G, ?_⟩
  filter_upwards
      [hG,
       avram_ubv_mixed13_original_finite_activity_physical_residual_uniform_compact_ae
         X hFinite] with ω hGω hCω
  refine ⟨hGω, ?_⟩
  intro K η hη
  obtain ⟨N, hN⟩ := hCω K η hη
  refine ⟨N, ?_⟩
  intro n hn T hTK
  have hEvent :
      ∀ᶠ m : ℕ in atTop,
        |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| ≤ η := by
    apply Filter.eventually_atTop.2
    refine ⟨n, ?_⟩
    intro m hnm
    exact le_of_lt (hN n m hn hnm T hTK)
  have hLim :
      Tendsto
        (fun m : ℕ =>
          |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
             avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω|)
        atTop
        (𝓝 |G T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω|) := by
    exact ((hGω T).sub_const _).abs
  calc
    |avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω - G T ω| =
        |G T ω - avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| :=
          abs_sub_comm _ _
    _ ≤ η := le_of_tendsto hLim hEvent
