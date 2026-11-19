-- Prove2me | solution 3 for AvramDividend.Classical.avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:55:42.561795+00:00
-- url     : https://prove2.me/submissions/1a7a97b4-911e-43b2-ae2f-9b7ce6798c49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Theorems.Thm_AvramDividend_Classical_avram_ja18_finite_range_optional_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18_rightcontinuous_clock_composition
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_finite_range_stopped_mart_terminal_condexp
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_UI_condexp_family_original_clock_L1_limit
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_F0_zero_under_physical_L1_mesh
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
  obtain ⟨ρ, hStop, hRange, hAbove, hBelow, hConv⟩ :=
    avram_ja18_original_rightcont_upper_grid_stops τ hτstop n hτbound
  let V : ℕ → Ω → ℝ := fun k ω => G (ρ k ω) ω
  have hGrid (k : ℕ) :
      Integrable (V k) P ∧
      (P[V k | 𝓕.rightCont 0] =ᵐ[P] (fun _ : Ω => (0 : ℝ))) := by
    obtain ⟨S, hS⟩ := hRange k
    exact avram_ja18_finite_range_optional_condexp_zero
      G (ρ k) (n : ℝ≥0) (hStop k) (hBelow k)
      S hS (fun t => (hGint t).1) hGcond hG0
  have hMeas (k : ℕ) :
      (hStop k).measurableSpace ≤ mΩ := by
    have hBound : ∀ ω, (ρ k ω : WithTop ℝ≥0) ≤ (n : WithTop ℝ≥0) := by
      intro ω
      exact_mod_cast hBelow k ω
    exact (hStop k).measurableSpace_le_of_le hBound
  have hCE (k : ℕ) :
      V k =ᵐ[P] P[G (n : ℝ≥0) | (hStop k).measurableSpace] := by
    obtain ⟨S, hS⟩ := hRange k
    exact avram_jump6_A_finite_range_stopped_mart_terminal_condexp
      G hGadapt (fun t => (hGint t).1) hGcond n (ρ k) (hStop k) (hBelow k) S hS
  have hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Set.Ici t) t := by
    filter_upwards [hGcont] with ω hω
    intro t
    exact (hω.continuousAt).continuousWithinAt
  have hValueConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => V k ω) atTop (nhds (G (τ ω) ω)) :=
    avram_ja18_rightcontinuous_clock_composition
      G τ ρ hRight hAbove hConv
  obtain ⟨hStopInt, hL1⟩ :=
    avram_jump6_A_UI_condexp_family_original_clock_L1_limit
      (G (n : ℝ≥0)) ((hGint (n : ℝ≥0)).1) V
      (fun k => (hStop k).measurableSpace) hMeas hCE
      (fun ω => G (τ ω) ω) hValueConv
  have hCenter :=
    avram_ubv_gauss13_stop_original_F0_zero_under_physical_L1_mesh
      X V (fun ω => G (τ ω) ω)
      (fun k => (hGrid k).1) (fun k => (hGrid k).2)
      hStopInt hL1
  have hStopEq :
      (fun ω => G (τ ω) ω) =ᵐ[P] (fun ω => R (τ ω) ω) := by
    filter_upwards [hGEq] with ω hω
    exact hω (τ ω)
  refine ⟨hStopInt.congr hStopEq, ?_⟩
  have hCEEq :
      P[(fun ω => R (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
        P[(fun ω => G (τ ω) ω) | 𝓕.rightCont 0] :=
    condExp_congr_ae hStopEq.symm
  exact hCEEq.trans hCenter
