-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_source_gaussian_adapted_rightcont_L1_martingale_exists_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:15:24.551054+00:00
-- url     : https://prove2.me/submissions/e15e65a4-de70-4953-a7e4-ef7b0d4cb965

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_canonical_adapted_ae_rightcont_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A source Gaussian martingale is globally adapted, zero-origin, L1 and almost surely right-continuous at all times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ t, Integrable (G t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by
  obtain ⟨R, hBoth, _, hL1, hMart⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hBoth] with ω hω
    exact hω.1
  have hRate : ∀ᵐ ω ∂P,
      ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
          R T ω| ≤ ε := by
    filter_upwards [hBoth] with ω hω
    exact hω.2
  obtain ⟨G, hAdapt, hZero, hRC, hEq⟩ :=
    avram_a24_original_gaussian_canonical_adapted_ae_rightcont_20261113
      X R hR hRate
  refine ⟨G, hAdapt, hZero, hRC, ?_, ?_⟩
  · intro t
    have hSym : (R t) =ᵐ[P] (G t) := by
      filter_upwards [hEq] with ω hω
      exact (hω t).symm
    exact (hL1 t).congr hSym
  · intro s t hst
    have hGt : (G t) =ᵐ[P] (R t) := by
      filter_upwards [hEq] with ω hω
      exact hω t
    have hCE : condExp (𝓕.rightCont s) P (G t) =ᵐ[P]
        condExp (𝓕.rightCont s) P (R t) :=
      condExp_congr_ae hGt
    filter_upwards [hCE, hMart s t hst, hEq] with ω hCEω hMω hGω
    calc
      condExp (𝓕.rightCont s) P (G t) ω =
        condExp (𝓕.rightCont s) P (R t) ω := hCEω
      _ = R s ω := hMω
      _ = G s ω := (hGω s).symm
