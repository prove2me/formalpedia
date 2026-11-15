-- Prove2me | solution 1 for AvramDividend.Classical.avram_a29_original_positive_sigma_intrinsic_gaussian_raw_allpath_cadlag
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:48:11.320828+00:00
-- url     : https://prove2.me/submissions/74691a40-e7e5-466f-8ce7-12d67c5ff9da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a66_original_finite_activity_causal_allpath_gaussian_regulariser_20261114
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
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ ω t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
        G t ω ≤ l) := by
  obtain ⟨G, hAdapt, hZero, hRight, hLeft, hNoPos, hPhysical⟩ :=
    avram_a66_original_finite_activity_causal_allpath_gaussian_regulariser_20261114
      X hX hFinite
  have hSource :=
    avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
      X hFinite R hR
  have hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω := by
    filter_upwards [hPhysical, hSource] with ω hGω hRω
    intro t
    exact (hGω t).trans (hRω t).symm
  exact ⟨G, hAdapt, hZero, hEq, hRight, hLeft, hNoPos⟩
