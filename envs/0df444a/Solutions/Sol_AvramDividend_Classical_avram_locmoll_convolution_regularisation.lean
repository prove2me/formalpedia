-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_convolution_regularisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:21:02.6313+00:00
-- url     : https://prove2.me/submissions/6452e20c-11e5-4886-b70e-e7d001b5447a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_c2
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_order
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_convolution_gradient
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (V ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hVsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    (∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) ∧
    ContDiff ℝ 2 g ∧ MonotoneOn g (Ici 0) ∧
    (∀ y : ℝ, 0 ≤ g y) ∧
    (∀ y : ℝ, y ≤ 0 → g y = 0) ∧
    (∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y) ∧
    (∀ y : ℝ, g y ≤ V y) := by 
  obtain ⟨hI, hg⟩ := avram_locmoll_convolution_c2 V ρ hVmono hρsmooth hρcompact
  obtain ⟨hm, hn, hz, hl⟩ := avram_locmoll_convolution_order V ρ δ hδ
    hVmono hVnonneg hVzero hVsec hρI hρnorm hρpos hρsupport hI
  exact ⟨hI, hg, hm, hn, hz,
    avram_locmoll_convolution_gradient V ρ δ hδ hVmono hVnonneg
      hVzero hVsec hρI hρnorm hρpos hρsupport hI hg, hl⟩
