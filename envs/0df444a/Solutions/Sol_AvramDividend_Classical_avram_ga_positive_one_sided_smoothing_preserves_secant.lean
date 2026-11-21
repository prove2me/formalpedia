-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_positive_one_sided_smoothing_preserves_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:38:14.155028+00:00
-- url     : https://prove2.me/submissions/21bef92b-5cd2-4967-a96f-71de91d59b66

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
noncomputable section
theorem solution
    (μ : Measure ℝ) (φ V : ℝ → ℝ)
    (hφI : Integrable φ μ)
    (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hV : ∀ x y : ℝ, x ≤ y → y - x ≤ V y - V x)
    (ε x y : ℝ) (hxy : x ≤ y)
    (hxI : Integrable (fun z => φ z * V (x - ε*z)) μ)
    (hyI : Integrable (fun z => φ z * V (y - ε*z)) μ) :
    y - x ≤
      (∫ z, φ z * V (y - ε*z) ∂μ) -
      (∫ z, φ z * V (x - ε*z) ∂μ)  := by
  have hpoint (z : ℝ) :
      y - x ≤ V (y - ε*z) - V (x - ε*z) := by
    convert hV (x - ε*z) (y - ε*z) (by linarith) using 1 <;> ring
  have hbound : ∀ᵐ z ∂μ,
      (y-x)*φ z ≤ φ z * V (y-ε*z) - φ z * V (x-ε*z) := by
    filter_upwards [hφpos] with z hz
    have h := mul_le_mul_of_nonneg_left (hpoint z) hz
    nlinarith
  have hi := integral_mono_ae
    (hφI.const_mul (y-x)) (hyI.sub hxI) hbound
  have hI : (∫ z, (y-x)*φ z ∂μ) ≤
      (∫ z, φ z * V (y-ε*z) ∂μ) -
      (∫ z, φ z * V (x-ε*z) ∂μ) := by
    calc
      _ ≤ ∫ z, φ z * V (y-ε*z) - φ z * V (x-ε*z) ∂μ := hi
      _ = _ := integral_sub hyI hxI
  simpa only [integral_const_mul, hφnorm, mul_one] using hI
