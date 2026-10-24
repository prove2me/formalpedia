-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponentially_damped_signed_primitive_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:45:42.989084+00:00
-- url     : https://prove2.me/submissions/37486d5b-a2f0-46f3-8100-74f581cb724a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A nonnegative exponential damping factor preserves pointwise signed
majorants after integration over a causal interval. -/
theorem solution
    (P F : ℝ → ℝ) (w x : ℝ)
    (hw : 0 ≤ w) (hx : 0 < x)
    (hPint : IntervalIntegrable
      (fun s : ℝ => Real.exp (-w * (x - s)) * P s) volume 0 x)
    (hFint : IntervalIntegrable F volume 0 x)
    (hdom : ∀ s ∈ Ioo (0 : ℝ) x, |P s| ≤ F s) :
    |∫ s in (0 : ℝ)..x, Real.exp (-w * (x - s)) * P s| ≤
      ∫ s in (0 : ℝ)..x, F s := by
  have hk : ∀ s ∈ Ioo (0 : ℝ) x,
      |Real.exp (-w * (x - s))| ≤ (1 : ℝ) := by
    intro s hs
    rw [Real.abs_exp]
    apply Real.exp_le_one_iff.mpr
    have hh : 0 ≤ w * (x - s) :=
      mul_nonneg hw (sub_nonneg.mpr hs.2.le)
    calc
      -w * (x - s) = -(w * (x - s)) := by ring
      _ ≤ 0 := neg_nonpos.mpr hh
  have hMajor : IntervalIntegrable
      (fun s : ℝ => (1 : ℝ) * F s) volume 0 x := by
    simpa only [one_mul] using hFint
  have hh := causal_signed_convolution_integral_abs_le_majorant
    (fun t : ℝ => Real.exp (-w * t)) (fun _ : ℝ => (1 : ℝ))
    P F x hx hPint hMajor hk hdom
    (by intro s hs; exact zero_le_one)
  simpa only [one_mul] using hh
