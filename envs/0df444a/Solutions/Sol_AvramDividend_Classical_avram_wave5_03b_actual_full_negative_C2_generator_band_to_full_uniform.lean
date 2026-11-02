-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_generator_band_to_full_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:09:44.4072+00:00
-- url     : https://prove2.me/submissions/49467dd6-fe65-4b9b-8d1a-3b9b93970180

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_full_negative_C2_source_generator_uniform_band_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform in all actual times and samples, retained finite negative Lévy
source bands approximate the full ruin-stopped nonlinear generator drift,
with one deterministic vanishing error bound for the original X,D. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ p : ℝ≥0 × Ω,
        ‖(∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
          (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)‖ₑ ≤ err n := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
    ∀ n : ℕ, ∀ p : ℝ≥0 × Ω,
      ‖(∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
        (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)‖ₑ ≤ err n
  obtain ⟨err, hErr, hBand⟩ :=
    avram_wave5_03b_actual_full_negative_C2_source_generator_uniform_band_tail
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv B hBm hBneg hBanti hBempty
  have hInt (p : ℝ≥0 × Ω) :
      Integrable (fun z : ℝ => JG (p,z))
        (X.ν.restrict (Iio (0 : ℝ))) :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv p
  have hSmallRestr (n : ℕ) :
      (X.ν.restrict (Iio (0 : ℝ))).restrict (B n) =
        X.ν.restrict (B n) := by
    rw [Measure.restrict_restrict (hBm n)]
    rw [Set.inter_eq_left.mpr (hBneg n)]
  have hBandRestr (n : ℕ) :
      (X.ν.restrict (Iio (0 : ℝ))).restrict (B n)ᶜ =
        X.ν.restrict (Iio (0 : ℝ) \ B n) := by
    rw [Measure.restrict_restrict (hBm n).compl]
    congr 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
    tauto
  have hSplit (n : ℕ) (p : ℝ≥0 × Ω) :
      (∫ z in B n, JG (p,z) ∂X.ν) +
      (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) := by
    have hs := integral_add_compl (s := B n)
      (μ := X.ν.restrict (Iio (0 : ℝ))) (hBm n) (hInt p)
    rw [hSmallRestr n, hBandRestr n] at hs
    exact hs
  have hPoint (n : ℕ) (p : ℝ≥0 × Ω) :
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
      (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν) =
      (∫ z in B n, JG (p,z) ∂X.ν) := by
    rw [← hSplit n p]
    ring
  refine ⟨err, hErr, ?_⟩
  intro n p
  rw [hPoint n p]
  exact hBand n p
