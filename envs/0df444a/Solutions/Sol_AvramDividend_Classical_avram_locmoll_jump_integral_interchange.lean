-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_jump_integral_interchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:47:08.413124+00:00
-- url     : https://prove2.me/submissions/02cc8a73-972a-4bdc-b4f5-cda7c02dd2de

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_actual_jump_product
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_actual_jump_pointwise
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_jump_fubini_core
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
    X.GeneratorIntegrable (fun t => ∫ r, ρ r * V (t - r)) y ∧
    Integrable (fun r => ρ r * (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w (y - r) z ∂X.ν)) ∧
    (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand
      (fun t => ∫ r, ρ r * V (t - r)) y z ∂X.ν) =
    (∫ r, ρ r * (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w (y - r) z ∂X.ν)) := by 
  let ν := X.ν.restrict (Iio 0)
  letI : SFinite ν := levy_negative_jump_measure_sFinite X
  have hP := avram_locmoll_actual_jump_product X q w V ρ C hC δ hδ
    hw_smooth hw_hjb hVeq hVmono hVnonneg hVzero hρI hρnorm
    hρpos hρsupport hρsmooth hρcompact hI hg y hy hyC hD1 hd1
  have he := avram_locmoll_actual_jump_pointwise X q w V ρ C hC δ hδ
    hw_smooth hw_hjb hVeq hVmono hVnonneg hVzero hρI hρnorm
    hρpos hρsupport hρsmooth hρcompact hI hg y hy hyC hD1 hd1
  have he' : ∀ᵐ z ∂ν, SpectrallyNegativeLevy.generatorIntegrand
      (fun t => ∫ r, ρ r * V (t - r)) y z =
      ∫ r, ρ r * SpectrallyNegativeLevy.generatorIntegrand w (y - r) z :=
    ae_restrict_of_forall_mem measurableSet_Iio he
  exact avram_locmoll_jump_fubini_core ν ρ
    (fun r z => SpectrallyNegativeLevy.generatorIntegrand w (y - r) z)
    (SpectrallyNegativeLevy.generatorIntegrand
      (fun t => ∫ r, ρ r * V (t - r)) y) hP he'
