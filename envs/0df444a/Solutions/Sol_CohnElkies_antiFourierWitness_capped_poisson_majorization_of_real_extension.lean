-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_capped_poisson_majorization_of_real_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/5d817999-9113-4cf2-b099-e92d649fa160

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_diffContOnCl
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_top_norm_le_one
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_differentiableOn_dimension
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_re_dimension
import Theorems.Thm_CohnElkies_horizontalStrip_norm_extension_majorization
import Theorems.Thm_CohnElkies_antiFourierWitness_cappedWeightedMellinStrip_growth

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (D : ℝ)
    (E : ℂ → ℝ)
    (hE : ContinuousOn E
      (Complex.im ⁻¹'
        Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)))
    (hEinterior : ∀ z : ℂ,
      z.im ∈ Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
        E z = (lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re)
    (hEbottom : ∀ z : ℂ,
      z.im = -((d : ℝ) / 2) →
        E z = lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D z.re)
    (hEtop : ∀ z : ℂ,
      z.im = (d : ℝ) / 2 → E z = 0)
    (hcap : ∀ y : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
        Real.exp (lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y))
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (s : ℝ) :
    ‖normalizedRadialMellinStrip hd w.function R
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))‖ ≤
      Real.exp
        (∫ T : ℝ, stripPoissonKernel σ T *
          lowerGammaBoundaryCapped
            ((d : ℝ) / 2) R D
            (s - ((d : ℝ) / 2) * T)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let S : Set ℂ := Complex.im ⁻¹' Icc (-ℓ) ℓ
  let Z : ℂ → ℂ :=
    normalizedRadialMellinStrip hd w.function R
  let W : ℂ → ℂ := lowerStripCappedGammaOuter ℓ R D
  let f : ℂ → ℂ := fun z => Complex.exp (-(W z)) * Z z
  let N : ℂ → ℝ := fun z => Real.exp (-(E z)) * ‖Z z‖
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  have hwidth : -ℓ < ℓ := by linarith
  have houter : DifferentiableOn ℂ W U := by
    exact lowerStripCappedGammaOuter_differentiableOn_dimension
      hd R D
  have hZdifferentiable : DifferentiableOn ℂ Z U := by
    exact (antiFourierWitness_normalizedMellinStrip_diffContOnCl
      hd w).differentiableOn
  have hf : DifferentiableOn ℂ f U := by
    exact houter.neg.cexp.mul hZdifferentiable
  have hclosure : closure U = S := by
    try dsimp [U, S]
    rw [Complex.closure_preimage_im,
      closure_Ioo (ne_of_lt hwidth)]
  have hZcontinuous : ContinuousOn Z S := by
    have hcont :=
      (antiFourierWitness_normalizedMellinStrip_diffContOnCl
        hd w).continuousOn
    simpa [Z, U, hclosure, ℓ] using! hcont
  have hN : ContinuousOn N S := by
    try dsimp [N]
    exact hE.neg.rexp.mul hZcontinuous.norm
  have hnonnegative : ∀ z : ℂ,
      z.im ∈ Icc (-ℓ) ℓ → 0 ≤ N z := by
    intro z hz
    exact mul_nonneg (Real.exp_pos _).le
      (norm_nonneg _)
  have hinterior : ∀ z : ℂ,
      z.im ∈ Ioo (-ℓ) ℓ → N z = ‖f z‖ := by
    intro z hz
    have hreal := hEinterior z hz
    try dsimp [N, f, W, Z]
    rw [hreal, norm_mul, Complex.norm_exp,
      Complex.neg_re]
  have hbottom : ∀ z : ℂ,
      z.im = -ℓ → N z ≤ (1 : ℝ) := by
    intro z hz
    have hrepr :
        (z.re : ℂ) - Complex.I * (ℓ : ℂ) = z := by
      apply Complex.ext
      · simp
      · simp [hz]
    have hzbound : ‖Z z‖ ≤
        Real.exp (lowerGammaBoundaryCapped ℓ R D z.re) := by
      rw [← hrepr]
      simpa [Z, ℓ] using! hcap z.re
    have hboundary := hEbottom z hz
    try dsimp [N]
    rw [hboundary]
    calc
      Real.exp
          (-(lowerGammaBoundaryCapped ℓ R D z.re)) *
          ‖Z z‖ ≤
        Real.exp
          (-(lowerGammaBoundaryCapped ℓ R D z.re)) *
          Real.exp
            (lowerGammaBoundaryCapped ℓ R D z.re) :=
          mul_le_mul_of_nonneg_left hzbound
            (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        simp
  have htop : ∀ z : ℂ,
      z.im = ℓ → N z ≤ (1 : ℝ) := by
    intro z hz
    have hrepr :
        (z.re : ℂ) + Complex.I * (ℓ : ℂ) = z := by
      apply Complex.ext
      · simp
      · simp [hz]
    have hzbound : ‖Z z‖ ≤ (1 : ℝ) := by
      rw [← hrepr]
      exact antiFourierWitness_normalizedMellinStrip_top_norm_le_one
        hd w z.re
    try dsimp [N]
    rw [hEtop z hz]
    simpa using! hzbound
  let z : ℂ := (s : ℂ) +
    Complex.I * (((σ * ℓ : ℝ) : ℂ))
  have hzbelow : -ℓ ≤ z.im := by
    try dsimp [z]
    simp only [Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.ofReal_re,
      zero_mul, Complex.I_im, one_mul, zero_add]
    nlinarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
  have hzabove : z.im ≤ ℓ := by
    try dsimp [z]
    simp only [Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.ofReal_re,
      zero_mul, Complex.I_im, one_mul, zero_add]
    nlinarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have hmax : N z ≤ (1 : ℝ) :=
    horizontalStrip_norm_extension_majorization
      hwidth (by norm_num) f N hf hN
      hnonnegative hinterior hbottom htop
      (antiFourierWitness_cappedWeightedMellinStrip_growth
        hd w D)
      hzbelow hzabove
  have hzinterior : z.im ∈ Ioo (-ℓ) ℓ := by
    try dsimp [z]
    simp only [Set.mem_Ioo,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, zero_mul, Complex.I_im,
      one_mul, zero_add]
    constructor
    · nlinarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · nlinarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have hreal := hEinterior z hzinterior
  have hpoisson := lowerStripCappedGammaOuter_re_dimension
    (R := R) (D := D) hd hbelow habove s
  have hEz : E z =
      ∫ T : ℝ,
        stripPoissonKernel σ T *
          lowerGammaBoundaryCapped ℓ R D (s - ℓ * T) := by
    calc
      E z = (lowerStripCappedGammaOuter ℓ R D z).re := hreal
      _ = _ := by
        simpa [z, ℓ] using! hpoisson
  have hweighted :
      Real.exp (-(E z)) * ‖Z z‖ ≤ (1 : ℝ) := hmax
  have hscale :=
    mul_le_mul_of_nonneg_left hweighted
      (Real.exp_pos (E z)).le
  have hfinal : ‖Z z‖ ≤ Real.exp (E z) := by
    convert! hscale using 1
    · rw [← mul_assoc, ← Real.exp_add]
      simp
    · simp
  rw [hEz] at hfinal
  simpa [z, Z, ℓ] using! hfinal
end CohnElkies
