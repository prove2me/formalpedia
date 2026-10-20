-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:09:08.822643+00:00
-- url     : https://prove2.me/submissions/3e5c9757-9fc0-415f-83fa-b08c61ef3cfb

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.analyticOn_of_dbar_eq_zero
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section
theorem solution {g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g z) (hdbar : ∀ z ∈ s, dbar g z = 0) :
    AnalyticOn ℂ g s := by 
  have hd : DifferentiableOn ℂ g s := by
    intro z hz
    refine (_root_.differentiableAt_complex_iff_differentiableAt_real.mpr ⟨hg z hz, ?_⟩).differentiableWithinAt
    have h := hdbar z hz
    unfold dbar at h
    have : fderiv ℝ g z Complex.I = Complex.I * fderiv ℝ g z 1 := by
      have h2 : Complex.I * (Complex.I * fderiv ℝ g z Complex.I) = - fderiv ℝ g z Complex.I := by
        rw [← mul_assoc, Complex.I_mul_I]; ring
      have h3 : Complex.I * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) = 0 := by rw [h, mul_zero]
      rw [mul_add, h2] at h3
      linear_combination -h3
    rw [this, smul_eq_mul]
  exact (hd.analyticOnNhd hs).analyticOn
