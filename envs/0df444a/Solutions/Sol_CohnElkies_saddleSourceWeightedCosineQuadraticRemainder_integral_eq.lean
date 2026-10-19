-- Prove2me | solution 1 for CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/d93d321e-2a4a-4983-b5a1-ca84d3723316

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (w : ℝ → ℝ) {b c : ℝ}
    (hbc : b ≤ c)
    (hw : ContinuousOn w (Icc b c))
    (u T : ℝ) :
    (∫ a in b..c,
      (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T) =
      (∫ a in b..c,
        (w a : ℂ) *
          (Complex.cos
            ((a : ℂ) *
              ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) -
        (∫ a in b..c,
          (w a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)) +
        Complex.I *
          ((T * ∫ a in b..c,
            w a * a * Real.sinh (u * a) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * ∫ a in b..c,
          w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun a =>
    (w a : ℂ) *
      (Complex.cos
        ((a : ℂ) *
          ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  let H : ℝ → ℝ := fun a =>
    w a * (Real.cosh (u * a) - 1)
  let L : ℝ → ℝ := fun a =>
    w a * a * Real.sinh (u * a)
  let V : ℝ → ℝ := fun a =>
    w a * a ^ 2 * Real.cosh (u * a)
  have hwc : ContinuousOn (fun a : ℝ => (w a : ℂ))
      (Icc b c) :=
    Complex.ofRealCLM.continuous.comp_continuousOn hw
  have hkernel : Continuous (fun a : ℝ =>
      Complex.cos
        ((a : ℂ) *
          ((T : ℂ) + Complex.I * (u : ℂ))) - 1) := by
    fun_prop
  have hF : IntervalIntegrable F volume b c :=
    (hwc.mul hkernel.continuousOn).intervalIntegrable_of_Icc
      hbc
  have hHreal : ContinuousOn H (Icc b c) := by
    try dsimp [H]
    exact hw.mul (by fun_prop)
  have hLreal : ContinuousOn L (Icc b c) := by
    try dsimp [L]
    exact (hw.mul continuous_id.continuousOn).mul
      (by fun_prop)
  have hVreal : ContinuousOn V (Icc b c) := by
    try dsimp [V]
    exact (hw.mul (continuous_id.pow 2).continuousOn).mul
      (by fun_prop)
  have hH : IntervalIntegrable
      (fun a : ℝ => (H a : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      hHreal).intervalIntegrable_of_Icc hbc
  have hL : IntervalIntegrable
      (fun a : ℝ => (L a : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      hLreal).intervalIntegrable_of_Icc hbc
  have hV : IntervalIntegrable
      (fun a : ℝ => (V a : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      hVreal).intervalIntegrable_of_Icc hbc
  have hlinear := hL.const_mul
    (Complex.I * (T : ℂ))
  have hquadratic := hV.const_mul
    (((T ^ 2 / 2 : ℝ) : ℂ))
  have hHcomplex :
      (∫ a in b..c, (H a : ℂ)) =
        ∫ a in b..c,
          (w a : ℂ) * ((Real.cosh (u * a) : ℂ) - 1) := by
    apply intervalIntegral.integral_congr
    intro a ha
    try dsimp [H]
    push_cast
    ring
  calc
    (∫ a in b..c,
      (w a : ℂ) *
        saddleSourceCosineQuadraticRemainder a u T) =
      ∫ a in b..c,
        (F a - (H a : ℂ) +
          (Complex.I * (T : ℂ)) * (L a : ℂ) +
          ((T ^ 2 / 2 : ℝ) : ℂ) * (V a : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro a ha
        try dsimp [F, H, L, V]
        unfold saddleSourceCosineQuadraticRemainder
        push_cast
        ring
    _ = ((∫ a in b..c, F a) -
          (∫ a in b..c, (H a : ℂ)) +
            (Complex.I * (T : ℂ)) *
              (∫ a in b..c, (L a : ℂ))) +
          ((T ^ 2 / 2 : ℝ) : ℂ) *
            (∫ a in b..c, (V a : ℂ)) := by
        rw [intervalIntegral.integral_add
          ((hF.sub hH).add hlinear) hquadratic]
        rw [intervalIntegral.integral_add
          (hF.sub hH) hlinear]
        rw [intervalIntegral.integral_sub hF hH]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    _ = _ := by
        rw [hHcomplex]
        conv_lhs =>
          rw [intervalIntegral.integral_ofReal,
            intervalIntegral.integral_ofReal]
        try dsimp only [F, L, V]
        simp only [Complex.ofReal_mul, Complex.ofReal_div,
          Complex.ofReal_pow, Complex.ofReal_ofNat]
        ring
end CohnElkies
