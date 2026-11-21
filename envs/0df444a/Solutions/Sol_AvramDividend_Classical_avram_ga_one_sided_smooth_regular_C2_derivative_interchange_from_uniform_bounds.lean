-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_one_sided_smooth_regular_C2_derivative_interchange_from_uniform_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:21:34.852232+00:00
-- url     : https://prove2.me/submissions/38796785-786f-49c0-89c1-e2620a8f82f1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_uniformly_dominated_weighted_smooth_shift_derivative_integral
open MeasureTheory Filter Set Topology AvramDividend.Classical
noncomputable section

theorem solution
    (μ : Measure ℝ) (φ f : ℝ → ℝ) (ε : ℝ)
    (hFI : ∀ y : ℝ, Integrable (fun z => φ z * f (y - ε * z)) μ)
    (hD1I : ∀ y : ℝ, Integrable
      (fun z => φ z * deriv f (y - ε * z)) μ)
    (hD2I : ∀ y : ℝ, Integrable
      (fun z => φ z * iteratedDeriv 2 f (y - ε * z)) μ)
    (hφI : Integrable (fun z => |φ z|) μ)
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hBd₁ : ∀ y, |deriv f y| ≤ L₁)
    (hBd₂ : ∀ y, |iteratedDeriv 2 f y| ≤ L₂)
    (hd₁ : ∀ y, HasDerivAt f (deriv f y) y)
    (hd₂ : ∀ y, HasDerivAt (deriv f) (iteratedDeriv 2 f y) y)
    (y : ℝ) :
    deriv (fun t => ∫ z, φ z * f (t - ε * z) ∂μ) y =
      ∫ z, φ z * deriv f (y - ε * z) ∂μ ∧
    iteratedDeriv 2 (fun t => ∫ z, φ z * f (t - ε * z) ∂μ) y =
      ∫ z, φ z * iteratedDeriv 2 f (y - ε * z) ∂μ := by
  let K : ℝ → ℝ := fun t => ∫ z, φ z * f (t - ε * z) ∂μ
  let K₁ : ℝ → ℝ := fun t => ∫ z, φ z * deriv f (t - ε * z) ∂μ
  let K₂ : ℝ → ℝ := fun t => ∫ z, φ z * iteratedDeriv 2 f (t - ε * z) ∂μ
  change deriv K y = K₁ y ∧ iteratedDeriv 2 K y = K₂ y
  have hfirst (t : ℝ) : deriv K t = K₁ t :=
    avram_ga_uniformly_dominated_weighted_smooth_shift_derivative_integral
      μ φ f (deriv f) ε t hFI hD1I hφI L₁ hL₁ hBd₁ hd₁
  have hsecond : deriv K₁ y = K₂ y :=
    avram_ga_uniformly_dominated_weighted_smooth_shift_derivative_integral
      μ φ (deriv f) (iteratedDeriv 2 f) ε y
      hD1I hD2I hφI L₂ hL₂ hBd₂ hd₂
  constructor
  · exact hfirst y
  · have he : deriv K =ᶠ[𝓝 y] K₁ :=
      Filter.Eventually.of_forall hfirst
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
      iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
    exact hsecond
