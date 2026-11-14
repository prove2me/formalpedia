-- Prove2me | solution 2 for AvramDividend.Classical.avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:28:30.827399+00:00
-- url     : https://prove2.me/submissions/530e5996-754c-42c1-a34e-49571b81c14a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Gaussian cutoff limit is integrable and mean zero by the existing source martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0,
      Integrable (R t) P ∧
      (∫ ω, R t ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨G, hGlim, hGmeas, hGint, hGMart⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  have hGsource : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (G T ω)) := by
    filter_upwards [hGlim] with ω hω
    exact hω.1
  have hUnique : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, R t ω = G t ω := by
    filter_upwards [hR, hGsource] with ω hωR hωG
    intro t
    exact tendsto_nhds_unique (hωR t) (hωG t)
  have hGzero : ∀ᵐ ω ∂P, G 0 ω = 0 :=
    avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
      X G hGsource
  intro t
  have hSame : (R t) =ᵐ[P] (G t) := by
    filter_upwards [hUnique] with ω hω
    exact hω t
  have hInt : Integrable (R t) P :=
    (hGint t).congr hSame.symm
  have hCondZero :
      P[(G t) | 𝓕.rightCont 0] =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    filter_upwards [hGMart 0 t (show (0 : ℝ≥0) ≤ t from zero_le), hGzero]
      with ω hω h0
    exact hω.trans h0
  have hGmean : (∫ ω, G t ω ∂P) = 0 := calc
    (∫ ω, G t ω ∂P) =
        (∫ ω, P[(G t) | 𝓕.rightCont 0] ω ∂P) :=
      (integral_condExp ((𝓕.rightCont).le 0)).symm
    _ = 0 := integral_eq_zero_of_ae hCondZero
  have hMean : (∫ ω, R t ω ∂P) = 0 := calc
    (∫ ω, R t ω ∂P) = (∫ ω, G t ω ∂P) :=
      integral_congr_ae hSame
    _ = 0 := hGmean
  exact ⟨hInt, hMean⟩
