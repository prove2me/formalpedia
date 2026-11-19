-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:26:34.762884+00:00
-- url     : https://prove2.me/submissions/59e038b0-f620-4e19-ae5e-14639c4c8b46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_continuous_L1_bounded_stop_initial_condexp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    Integrable (fun ω => R (τ ω) ω) P ∧
      P[(fun ω => R (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨G, hGmeas, hGzero, hGEq, hGcont, _, _, hGint, hGcond⟩ :=
    avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
      X hX hFinite R hR
  have hGadapt : ∀ t : ℝ≥0, Measurable[𝓕.rightCont t] (G t) := by
    intro t
    exact (hGmeas t).mono (𝓕.le_rightCont t) le_rfl
  have hG0 : ∀ᵐ ω ∂P, G 0 ω = 0 :=
    Filter.Eventually.of_forall hGzero
  obtain ⟨hGI, hGC⟩ :=
    avram_jump6_A_continuous_L1_bounded_stop_initial_condexp
      G hGadapt hG0 hGcont (fun t => (hGint t).1)
      hGcond n hn τ hτstop hτbound
  have hStopEq :
      (fun ω => G (τ ω) ω) =ᵐ[P] (fun ω => R (τ ω) ω) := by
    filter_upwards [hGEq] with ω hω
    exact hω (τ ω)
  refine ⟨hGI.congr hStopEq, ?_⟩
  have hCEEq :
      P[(fun ω => R (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
        P[(fun ω => G (τ ω) ω) | 𝓕.rightCont 0] :=
    condExp_congr_ae hStopEq.symm
  exact hCEEq.trans hGC
