-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_canonical_gaussian_adapted_centered_martingale_rightcont_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:16:50.499975+00:00
-- url     : https://prove2.me/submissions/47116589-5955-4a2d-8458-a02196014352

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_a24_canonical_gaussian_martingale_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian canonical adapted centred martingale has conull right-continuous paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by
  obtain ⟨R, hLimit, _, _, hMart⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  have hRate : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
          R T ω| ≤ ε := by
    filter_upwards [hLimit] with ω hω
    exact hω.2
  obtain ⟨G, hAdapt, hZero, hEq, hGmart⟩ :=
    avram_a24_canonical_gaussian_martingale_20261114 X R hR hMart
  have hRC := avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
    X R hRate
  have hMom :=
    avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
      X hX hFinite R hR
  refine ⟨G, hAdapt, hZero, ?_, ?_, hGmart⟩
  · filter_upwards [hEq, hRC] with ω hω hωRC
    intro t
    have hPath : (fun u : ℝ≥0 => G u ω) = (fun u => R u ω) := by
      funext u
      exact hω u
    simpa only [hPath] using hωRC t
  · intro t
    have hCongr : (fun ω => R t ω) =ᵐ[P] (G t) := by
      filter_upwards [hEq] with ω hω
      exact (hω t).symm
    have hInt : Integrable (G t) P := (hMom t).1.congr hCongr
    refine ⟨hInt, ?_⟩
    calc
      (∫ ω, G t ω ∂P) = (∫ ω, R t ω ∂P) := integral_congr_ae hCongr.symm
      _ = 0 := (hMom t).2
