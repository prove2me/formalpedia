-- Prove2me | solution 1 for CohnElkies.lowerStripGammaOuter_integrable_of_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/80ceac1e-00b2-41b5-a348-093896e82863

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzAngle_mem_Ioo
import Theorems.Thm_CohnElkies_norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
import Theorems.Thm_CohnElkies_norm_stripRegularizedHolomorphicPoissonKernel_of_neg
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_continuousOn

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ R : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (hgamma : Integrable
      (fun y : ℝ =>
        Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
          lowerGammaBoundaryLog ℓ R y)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ z y *
          (lowerGammaBoundaryLog ℓ R y : ℂ)) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  let a : ℝ := Real.pi / (2 * ℓ)
  let D : ℝ :=
    2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))
  let Cpos : ℝ := Real.exp (a * z.re) / D
  let Cneg : ℝ := Real.exp (-a * z.re) / D
  have ha : 0 < a := by
    try dsimp [a]
    exact div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  change Integrable
    (fun y : ℝ =>
      Real.exp ((-a) * |y|) * lowerGammaBoundaryLog ℓ R y)
    at hgamma
  have hgammaabs :
      Integrable
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) * |lowerGammaBoundaryLog ℓ R y|) := by
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)] using! hgamma.norm
  have hposfactor (y : ℝ) :
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D =
        Cpos * Real.exp ((-a) * y) := by
    have hsplit :
        Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) =
          Real.exp (a * z.re) * Real.exp ((-a) * y) := by
      rw [← Real.exp_add]
      congr 1
      try dsimp [a]
      ring
    rw [hsplit]
    try dsimp [Cpos]
    ring
  have hnegfactor (y : ℝ) :
      Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D =
        Cneg * Real.exp (a * y) := by
    have hsplit :
        Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) =
          Real.exp (-a * z.re) * Real.exp (a * y) := by
      rw [← Real.exp_add]
      congr 1
      try dsimp [a]
      ring
    rw [hsplit]
    try dsimp [Cneg]
    ring
  have hgammaRight :
      ContinuousOn (lowerGammaBoundaryLog ℓ R) (Ioi (0 : ℝ)) :=
    lowerGammaBoundaryLog_continuousOn hℓ R
      (fun y hy => (mem_Ioi.mp hy).ne')
  have hcastRight :
      ContinuousOn
        (fun y : ℝ => (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Ioi (0 : ℝ)) := by
    simpa [Function.comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hgammaRight
  have hcontinuousRight :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Ioi (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
      hℓ hz).mul hcastRight
  have hrightmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cpos *
            (Real.exp ((-a) * |y|) *
              |lowerGammaBoundaryLog ℓ R y|))
        (Ioi (0 : ℝ)) :=
    hgammaabs.integrableOn.const_mul Cpos
  have hright :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Ioi (0 : ℝ)) := by
    apply hrightmajorant.mono'
      (hcontinuousRight.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (lowerGammaBoundaryLog ℓ R y : ℂ)‖ ≤
        Cpos *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbound :=
      norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
        hℓ hz (mem_Ioi.mp hy).le
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
        Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D
      at hbound
    calc
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ *
          |lowerGammaBoundaryLog ℓ R y| ≤
        (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D) *
          |lowerGammaBoundaryLog ℓ R y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cpos *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|) := by
        rw [abs_of_pos (mem_Ioi.mp hy), hposfactor]
        ring
  have hgammaLeft :
      ContinuousOn (lowerGammaBoundaryLog ℓ R) (Iio (0 : ℝ)) :=
    lowerGammaBoundaryLog_continuousOn hℓ R
      (fun y hy => (mem_Iio.mp hy).ne)
  have hcastLeft :
      ContinuousOn
        (fun y : ℝ => (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Iio (0 : ℝ)) := by
    simpa [Function.comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hgammaLeft
  have hcontinuousLeft :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Iio (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio
      hℓ hz).mul hcastLeft
  have hleftmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cneg *
            (Real.exp ((-a) * |y|) *
              |lowerGammaBoundaryLog ℓ R y|))
        (Iio (0 : ℝ)) :=
    hgammaabs.integrableOn.const_mul Cneg
  have hleft :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Iio (0 : ℝ)) := by
    apply hleftmajorant.mono'
      (hcontinuousLeft.aestronglyMeasurable measurableSet_Iio)
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (lowerGammaBoundaryLog ℓ R y : ℂ)‖ ≤
        Cneg *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbound :=
      norm_stripRegularizedHolomorphicPoissonKernel_of_neg
        hℓ hz (mem_Iio.mp hy)
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
        Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D
      at hbound
    calc
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ *
          |lowerGammaBoundaryLog ℓ R y| ≤
        (Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D) *
          |lowerGammaBoundaryLog ℓ R y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cneg *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|) := by
        rw [abs_of_neg (mem_Iio.mp hy), hnegfactor]
        simp [mul_neg, neg_mul]
        ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩
end CohnElkies
