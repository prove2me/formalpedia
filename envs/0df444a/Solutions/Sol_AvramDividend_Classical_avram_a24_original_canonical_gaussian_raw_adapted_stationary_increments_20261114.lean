-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_canonical_gaussian_raw_adapted_stationary_increments_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:08:02.046586+00:00
-- url     : https://prove2.me/submissions/c5c5d8ea-7f1a-4c23-9580-ad4aac1fd52d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The globally source-adapted Gaussian residual has a stationary-increment law at every deterministic start. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) ∧
      (∀ T : ℝ≥0, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) := by
  obtain ⟨G, hAdapt, hZero, hEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  refine ⟨G, hAdapt, hZero, hEq, ?_⟩
  intro T
  obtain ⟨Z, hZ, hStat⟩ :=
    avram_a24_original_gaussian_limit_increment_stationary_law_20261113
      X hX hFinite R hR T
  refine ⟨Z, hZ, ?_⟩
  intro s
  have hCongr : (fun ω => G (s + T) ω - G s ω) =ᵐ[P]
      (fun ω => R (s + T) ω - R s ω) := by
    filter_upwards [hEq] with ω hω
    rw [hω (s + T), hω s]
  calc
    Measure.map (fun ω => G (s + T) ω - G s ω) P =
      Measure.map (fun ω => R (s + T) ω - R s ω) P :=
        Measure.map_congr hCongr
    _ = Measure.map Z P := hStat s
