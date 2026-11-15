-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:26:39.30761+00:00
-- url     : https://prove2.me/submissions/8eee49bf-8805-4c97-b0cf-333fb1b619b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
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
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    {ι : Type*} (S : Finset ι)
    (a b : ι → ℝ≥0) (WG WJ : ι → Ω → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
    (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (LG LJ : ℝ) (hLG : 0 ≤ LG) (hLJ : 0 ≤ LJ)
    (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG)
    (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) :
    Integrable (fun ω => ∑ i ∈ S,
      (if τ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) P ∧
    Integrable (fun ω => ∑ i ∈ S,
      (if τ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) P := by
  obtain ⟨R0, J0, hR0, hJ0, hGrid⟩ :=
    AvramDividend.Classical.avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
      X hX hFinite
  have hReq : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, R u ω = R0 u ω := by
    filter_upwards [hR, hR0] with ω hRω hR0ω
    intro u
    exact tendsto_nhds_unique (hRω u) (hR0ω u)
  have hJeq : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Jsmall u ω = J0 u ω := by
    filter_upwards [hJ, hJ0] with ω hJω hJ0ω
    intro u
    exact tendsto_nhds_unique (hJω u) (hJ0ω u)
  obtain ⟨hIG0, _, hIJ0, _⟩ :=
    hGrid S a b WG WJ hab hWG hWJ τ hτstop
      LG LJ hLG hLJ hWGbound hWJbound
  have hGae :
      (fun ω => ∑ i ∈ S,
        (if τ ω ≤ a i then 0 else WG i ω) *
          (R0 (b i) ω - R0 (a i) ω)) =ᵐ[P]
      (fun ω => ∑ i ∈ S,
        (if τ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)) := by
    filter_upwards [hReq] with ω hω
    apply Finset.sum_congr rfl
    intro i hi
    simp only [← hω (b i), ← hω (a i)]
  have hJae :
      (fun ω => ∑ i ∈ S,
        (if τ ω ≤ a i then 0 else WJ i ω) *
          (J0 (b i) ω - J0 (a i) ω)) =ᵐ[P]
      (fun ω => ∑ i ∈ S,
        (if τ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) := by
    filter_upwards [hJeq] with ω hω
    apply Finset.sum_congr rfl
    intro i hi
    simp only [← hω (b i), ← hω (a i)]
  exact ⟨hIG0.congr hGae, hIJ0.congr hJae⟩
