-- Prove2me | solution 1 for CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/bf9e67de-dff4-459c-8499-ba7fea1caa14

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceCosineQuadraticRemainder_norm_le

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
    (hb : 0 ≤ b)
    (hw : ContinuousOn w (Icc b c))
    (hwnonneg : ∀ a ∈ Icc b c, 0 ≤ w a)
    (u T : ℝ) :
    ‖∫ a in b..c,
        (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        ∫ a in b..c,
          w a * a ^ 3 * Real.cosh (u * a) := by
  let g : ℝ → ℝ := fun a =>
    (|T| ^ 3 / 6) *
      (w a * a ^ 3 * Real.cosh (u * a))
  have hbase : ContinuousOn
      (fun a : ℝ => w a * a ^ 3 * Real.cosh (u * a))
      (Icc b c) :=
    (hw.mul (continuous_id.pow 3).continuousOn).mul
      (by fun_prop)
  have hg : IntervalIntegrable g volume b c := by
    try dsimp [g]
    exact (continuousOn_const.mul hbase).intervalIntegrable_of_Icc
      hbc
  have hpoint (a : ℝ) (ha : a ∈ Ioc b c) :
      ‖(w a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
        g a := by
    have hmem : a ∈ Icc b c := ⟨ha.1.le, ha.2⟩
    have hwa : 0 ≤ w a := hwnonneg a hmem
    have haa : 0 ≤ a := hb.trans ha.1.le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hwa]
    calc
      w a * ‖saddleSourceCosineQuadraticRemainder a u T‖ ≤
        w a *
          (Real.cosh (u * a) * |a * T| ^ 3 / 6) :=
            mul_le_mul_of_nonneg_left
              (saddleSourceCosineQuadraticRemainder_norm_le
                a u T)
              hwa
      _ = g a := by
        try dsimp [g]
        rw [abs_mul, abs_of_nonneg haa]
        ring
  calc
    ‖∫ a in b..c,
        (w a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
      ∫ a in b..c, g a := by
        apply intervalIntegral.norm_integral_le_of_norm_le
          hbc _ hg
        filter_upwards [] with a ha
        exact hpoint a ha
    _ = (|T| ^ 3 / 6) *
      ∫ a in b..c,
        w a * a ^ 3 * Real.cosh (u * a) := by
        try dsimp [g]
        rw [intervalIntegral.integral_const_mul]
end CohnElkies
