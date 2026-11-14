-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB46_original_BV_full_negative_mark_loss_integral_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:18:49.789238+00:00
-- url     : https://prove2.me/submissions/2d50f713-92ad-4e35-834a-1bc9e9b04a44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (c ε L M K : ℝ)
    (hε : 0 < ε) (hεc : ε ≤ c) (hε2 : ε ≤ 2)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * M ≤ K * (ε / 2))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hBound : ∀ r ∈ Icc (0 : ℝ) c, |w r| ≤ M)
    (hLip : ∀ a ∈ Icc (ε / 2) c, ∀ b ∈ Icc (ε / 2) c,
      |w a - w b| ≤ L * |a - b|)
    (y : ℝ) (hy : y ∈ Icc ε c)
    (hGen : X.GeneratorIntegrable w y) :
    -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
      ∫ z in Iio (0 : ℝ),
        (if -(ε / 2) ≤ z then L * |z| else 2 * M) ∂X.ν := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let f : ℝ → ℝ := fun z => w (y + z) - w y
  let g : ℝ → ℝ := fun z =>
    if -(ε / 2) ≤ z then L * |z| else 2 * M
  have hf : Integrable f μ :=
    boundedVariation_full_negative_jump_increment_integrable
      X hBV w y hGen
  have hg : Integrable g μ :=
    avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
      X hBV ε L M K hε hε2 hL hM hK hKL hKM
  have hAE : ∀ᵐ z ∂μ, -f z ≤ g z := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    have hBoundZ :=
      avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
        w c ε L M hε hεc hL hM hwNeg hBound hLip y z hy hz
    have hg0 : 0 ≤ g z := by
      dsimp [g]
      split_ifs
      · positivity
      · positivity
    change ‖f z‖ ≤ ‖g z‖ at hBoundZ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg0] at hBoundZ
    exact (neg_le_abs (f z)).trans hBoundZ
  have hIntegral := integral_mono_ae hf.neg hg hAE
  change -(∫ z, f z ∂μ) ≤ ∫ z, g z ∂μ
  have hNegInt : (∫ z, -f z ∂μ) = -(∫ z, f z ∂μ) :=
    integral_neg _
  calc
    -(∫ z, f z ∂μ) = ∫ z, -f z ∂μ := hNegInt.symm
    _ ≤ ∫ z, g z ∂μ := hIntegral
