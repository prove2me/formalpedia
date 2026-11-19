-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_finiteactivity_fullmark_stopped_martingale_physical_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:50:39.78221+00:00
-- url     : https://prove2.me/submissions/8bdca8c8-e9c8-498f-8559-7d41cad0b0ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin15_original_compensated_jump_stopped_martingale_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The genuine full negative-jump martingale is the sum of original small marks, large marks and compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    ∃ Jfull : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
            (t : ℝ) * (X.c - μ)) ∧
      (∀ t : ℝ≥0, Integrable (Jfull t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jfull t) ω = Jfull s ω) ∧
      Integrable (fun ω => Jfull (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => Jfull (τ ω) ω) ω = 0) := by
  have hFull :=
    avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
      X R Jsmall hR hJ
  have hStop :=
    avram_mix_fin15_original_compensated_jump_stopped_martingale_public
      X hX hFinite R hR hRint hRmart n hn τ hτstop hτbound
  dsimp only at hStop
  rcases hStop with ⟨hInt, hMart, hStopInt, hZero⟩
  let μ : ℝ := ∫ ω, X.X 1 ω ∂P
  let Jfull : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
  refine ⟨Jfull, ?_, hInt, hMart, hStopInt, hZero⟩
  filter_upwards [hFull] with ω hω
  intro t
  dsimp [Jfull, μ]
  have hh := hω t
  linarith
