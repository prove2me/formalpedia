-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_actual_jump_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:46:26.092044+00:00
-- url     : https://prove2.me/submissions/2633e18c-fd20-4d47-93e6-e35a15b4511d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_weighted_jump_product
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_jump_shifted_agreement
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w V ρ : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (δ : ℝ) (hδ : 0 < δ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hVeq : ∀ y : ℝ, ENNReal.ofReal y ≤ C → V y = w y)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ)
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r)))
    (hg : ContDiff ℝ 2 (fun y => ∫ r, ρ r * V (y - r)))
    (y : ℝ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C)
    (hD1 : Integrable (fun r => ρ r * deriv w (y - r)))
    (hd1 : deriv (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * deriv w (y - r))) :
    Integrable (fun p : ℝ × ℝ => ρ p.1 *
      SpectrallyNegativeLevy.generatorIntegrand w (y - p.1) p.2)
      (volume.prod (X.ν.restrict (Iio 0))) := by 
  let ν := X.ν.restrict (Iio 0)
  letI : SFinite ν := levy_negative_jump_measure_sFinite X
  obtain ⟨hVc, hd, hv, he⟩ := avram_locmoll_jump_shifted_agreement
    w V C δ y hδ hy hyC hw_smooth hVeq
  have hs : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      y - r ∈ Icc (y - 2 * (δ / 3)) (y - δ / 3) := by
    filter_upwards [hρsupport] with r hr
    intro hne
    exact ⟨by linarith [(hr hne).2], by linarith [(hr hne).1]⟩
  have hP := avram_locmoll_weighted_jump_product X V ρ y
    (y - 2 * (δ / 3)) (y - δ / 3) (by linarith) (by linarith)
    (by linarith) hVmono hVnonneg hVc hρI hρsmooth.continuous.measurable hs
  apply hP.congr
  have hs' : ∀ᵐ p ∂volume.prod ν, ρ p.1 ≠ 0 →
      p.1 ∈ Icc (δ / 3) (2 * (δ / 3)) :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := ν)).tendsto_ae.eventually hρsupport
  have hz' : ∀ᵐ p : ℝ × ℝ ∂volume.prod ν, p.2 < 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := ν)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Iio)
  filter_upwards [hs', hz'] with p hp hz
  by_cases hzero : ρ p.1 = 0
  · simp [hzero]
  · rw [he p.1 (hp hzero) p.2 hz]
