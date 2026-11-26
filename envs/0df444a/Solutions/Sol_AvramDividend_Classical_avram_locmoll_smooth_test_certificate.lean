-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_smooth_test_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:59:39.725988+00:00
-- url     : https://prove2.me/submissions/10e4bfa8-1a41-40bf-8484-853537930764

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_cap_extension
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_normalised_kernel
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_regularisation
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_generator_convolution_hjb
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (δ : ℝ) (hδ : 0 < δ) (hδx : δ < x) :
    ∃ (V ρ g : ℝ → ℝ),
      Integrable ρ ∧ (∫ r, ρ r) = 1 ∧
      (0 ≤ᵐ[volume] ρ) ∧
      (∀ᵐ r ∂volume, ρ r ≠ 0 →
        r ∈ Icc (δ / 3) (2 * (δ / 3))) ∧
      (∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u) ∧
      (∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) ∧
      (∀ y : ℝ, g y = ∫ r, ρ r * V (y - r)) ∧
      ContDiff ℝ 2 g ∧ MonotoneOn g (Ici 0) ∧
      (∀ y : ℝ, 0 ≤ g y) ∧
      (∀ y : ℝ, y ≤ 0 → g y = 0) ∧
      (∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y) ∧
      (∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
        X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0) ∧
      g x ≤ w x := by 
  have hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyc
    have h := le_max_right (X.generator w y - q * w y) (1 - deriv w y)
    rw [(hw_hjb y hy hyc).2] at h
    linarith
  have hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyc
    refine ⟨(hw_hjb y hy hyc).1, ?_⟩
    have h := le_max_left (X.generator w y - q * w y) (1 - deriv w y)
    rwa [(hw_hjb y hy hyc).2] at h
  obtain ⟨V, hVeq, hVzero, hVnonneg, hVmono, hVsec⟩ :=
    avram_locmoll_cap_extension C hC w hw_cont hw0 hw_neg
      (hw_smooth.of_le (by norm_num)) hgrad
  obtain ⟨ρ, hρI, hρnorm, hρpos, hρsupport, hρsmooth, hρcompact⟩ :=
    avram_locmoll_normalised_kernel δ hδ
  obtain ⟨hI, hg, hmono, hnonneg, hzero, hgradg, hle⟩ :=
    avram_locmoll_convolution_regularisation V ρ δ hδ
      hVmono hVnonneg hVzero hVsec hρI hρnorm hρpos hρsupport
      hρsmooth hρcompact
  refine ⟨V, ρ, (fun y => ∫ r, ρ r * V (y - r)), hρI, hρnorm,
    hρpos, hρsupport, hVsec, hI, fun _ => rfl, hg, hmono,
    hnonneg, hzero, hgradg, ?_, ?_⟩
  · exact avram_locmoll_generator_convolution_hjb X q w V ρ C hC
      δ hδ hw_smooth hgen hVeq hVmono hVnonneg hVzero hρI
      hρnorm hρpos hρsupport hρsmooth hρcompact hI hg
  · exact (hle x).trans (le_of_eq (hVeq x hxc))
