-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_interior_jet_interchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:42:37.63784+00:00
-- url     : https://prove2.me/submissions/f1fb18dc-9fda-4af2-932f-4b05900d3899

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_local_window_extension
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_translated_jet_transfer
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
    (y : ℝ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    Integrable (fun r => ρ r * w (y - r)) ∧
    Integrable (fun r => ρ r * deriv w (y - r)) ∧
    Integrable (fun r => ρ r * iteratedDeriv 2 w (y - r)) ∧
    (∫ r, ρ r * V (y - r)) = (∫ r, ρ r * w (y - r)) ∧
    deriv (fun t => ∫ r, ρ r * V (t - r)) y = (∫ r, ρ r * deriv w (y - r)) ∧
    iteratedDeriv 2 (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * iteratedDeriv 2 w (y - r)) := by 
  obtain ⟨F, hF, hFc, he⟩ := avram_locmoll_local_window_extension
    w V C δ y hδ hy hyC hw_smooth hVeq
  exact avram_locmoll_translated_jet_transfer w V F ρ δ y hδ hρI
    hρsupport hF hFc he
