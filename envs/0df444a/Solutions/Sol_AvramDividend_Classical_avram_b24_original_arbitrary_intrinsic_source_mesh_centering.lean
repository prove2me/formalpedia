-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_source_mesh_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:01:53.040886+00:00
-- url     : https://prove2.me/submissions/2a156b76-d992-4481-a20b-f35eb389acff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
import Theorems.Thm_AvramDividend_Classical_avram_b24_intrinsic_same_source_noise_limits_unique
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
        atTop (𝓝 (Jsmall u ω))) :
    ∀ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
      (WG WJ : ℕ → Ω → ℝ)
      (hab : ∀ i ∈ S, a i ≤ b i)
      (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
      (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
      (σ : Ω → ℝ≥0)
      (hσstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (σ ω : WithTop ℝ≥0)))
      (LG LJ : ℝ) (hLG : 0 ≤ LG) (hLJ : 0 ≤ LJ)
      (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG)
      (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ),
      let MG : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)
      let MJ : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)
      Integrable MG P ∧
      P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable MJ P ∧
      P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  obtain ⟨R0, J0, hR0, hJ0, hcentred⟩ :=
    avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
      X hX hFinite
  have hUnique :=
    (avram_b24_intrinsic_same_source_noise_limits_unique
      X R R0 Jsmall J0 hR hR0 hJ hJ0).2
  intro S a b WG WJ hab hWG hWJ σ hσstop LG LJ hLG hLJ hWGbound hWJbound
  obtain ⟨hGint, hGzero, hJint, hJzero⟩ :=
    hcentred S a b WG WJ hab hWG hWJ σ hσstop
      LG LJ hLG hLJ hWGbound hWJbound
  have hMeshEqual := hUnique S a b WG WJ σ
  have hGae := hMeshEqual.mono (fun ω hω => hω.1)
  have hJae := hMeshEqual.mono (fun ω hω => hω.2)
  exact ⟨hGint.congr (Filter.EventuallyEq.symm hGae),
    (condExp_congr_ae hGae).trans hGzero,
    hJint.congr (Filter.EventuallyEq.symm hJae),
    (condExp_congr_ae hJae).trans hJzero⟩
