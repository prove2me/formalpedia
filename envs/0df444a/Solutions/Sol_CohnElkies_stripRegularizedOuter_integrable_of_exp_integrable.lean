-- Prove2me | solution 1 for CohnElkies.stripRegularizedOuter_integrable_of_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/47741f95-0211-4f63-a6cf-4b4bb5c1e7d7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzAngle_mem_Ioo
import Theorems.Thm_CohnElkies_norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
import Theorems.Thm_CohnElkies_norm_stripRegularizedHolomorphicPoissonKernel_of_neg
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hboundary : Integrable
      (fun y : ℝ =>
        Real.exp (-(Real.pi / (2 * ℓ)) * |y|) * b y)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ z y *
          (b y : ℂ)) := by
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
      Real.exp ((-a) * |y|) * b y)
    at hboundary
  have hboundaryabs :
      Integrable
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) * |b y|) := by
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)] using! hboundary.norm
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
  have hboundaryRight :
      ContinuousOn b (Ioi (0 : ℝ)) :=
    hb.continuousOn
  have hcastRight :
      ContinuousOn
        (fun y : ℝ => (b y : ℂ))
        (Ioi (0 : ℝ)) := by
    simpa [Function.comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hboundaryRight
  have hcontinuousRight :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Ioi (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
      hℓ hz).mul hcastRight
  have hrightmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cpos *
            (Real.exp ((-a) * |y|) *
              |b y|))
        (Ioi (0 : ℝ)) :=
    hboundaryabs.integrableOn.const_mul Cpos
  have hright :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Ioi (0 : ℝ)) := by
    apply hrightmajorant.mono'
      (hcontinuousRight.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (b y : ℂ)‖ ≤
        Cpos *
          (Real.exp ((-a) * |y|) *
            |b y|)
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
          |b y| ≤
        (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D) *
          |b y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cpos *
          (Real.exp ((-a) * |y|) *
            |b y|) := by
        rw [abs_of_pos (mem_Ioi.mp hy), hposfactor]
        ring
  have hboundaryLeft :
      ContinuousOn b (Iio (0 : ℝ)) :=
    hb.continuousOn
  have hcastLeft :
      ContinuousOn
        (fun y : ℝ => (b y : ℂ))
        (Iio (0 : ℝ)) := by
    simpa [Function.comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hboundaryLeft
  have hcontinuousLeft :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Iio (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio
      hℓ hz).mul hcastLeft
  have hleftmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cneg *
            (Real.exp ((-a) * |y|) *
              |b y|))
        (Iio (0 : ℝ)) :=
    hboundaryabs.integrableOn.const_mul Cneg
  have hleft :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Iio (0 : ℝ)) := by
    apply hleftmajorant.mono'
      (hcontinuousLeft.aestronglyMeasurable measurableSet_Iio)
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (b y : ℂ)‖ ≤
        Cneg *
          (Real.exp ((-a) * |y|) *
            |b y|)
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
          |b y| ≤
        (Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D) *
          |b y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cneg *
          (Real.exp ((-a) * |y|) *
            |b y|) := by
        rw [abs_of_neg (mem_Iio.mp hy), hnegfactor]
        simp [mul_neg, neg_mul]
        ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩
end CohnElkies
