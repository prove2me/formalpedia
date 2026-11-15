-- Prove2me | solution 1 for AvramDividend.Classical.avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:24:19.450197+00:00
-- url     : https://prove2.me/submissions/df44034b-6d8f-4782-aa24-513b04974d1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
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
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) := by
  obtain ⟨G, hAdapt, hZero, hEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113
      X R hR
  have hContinuity :=
    avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
      X hFinite R hR
  refine ⟨G, hAdapt, hZero, hEq, ?_⟩
  filter_upwards [hEq, hContinuity] with ω hGω hRω
  have hPath : (fun t : ℝ≥0 => G t ω) =
      (fun t : ℝ≥0 => R t ω) := by
    funext t
    exact hGω t
  simpa only [hPath] using hRω
