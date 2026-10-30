-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_perpetual_esscher_renewal_cancel_to_scale_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:12:01.648503+00:00
-- url     : https://prove2.me/submissions/0c519fc1-f00b-4922-a179-b8f1487401bd

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory

/-- Cancellation of the genuine perpetual Esscher renewal against the common
positive-root normalised scale CDF, retaining the original reserve shift. -/
theorem solution
    (φ m x a K Cx Ca : ℝ) (W : ℝ → ℝ)
    (hm : 0 < m) (hWa : 0 < W a)
    (hCx : Cx = m * Real.exp (-(φ * x)) * W x)
    (hCa : Ca = m * Real.exp (-(φ * a)) * W a)
    (hRenew : Cx = Real.exp (φ * (a - x)) * Ca * K) :
    K = W x / W a := by
  have hExp :
      Real.exp (φ * (a - x)) * Real.exp (-(φ * a)) =
        Real.exp (-(φ * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hCx, hCa] at hRenew
  have hEq :
      (m * Real.exp (-(φ * x))) * W x =
        (m * Real.exp (-(φ * x))) * (W a * K) := by
    calc
      (m * Real.exp (-(φ * x))) * W x =
          Real.exp (φ * (a - x)) *
            (m * Real.exp (-(φ * a)) * W a) * K := hRenew
      _ = (m * (Real.exp (φ * (a - x)) *
            Real.exp (-(φ * a)))) * (W a * K) := by ring
      _ = (m * Real.exp (-(φ * x))) * (W a * K) := by rw [hExp]
  have hCommon : m * Real.exp (-(φ * x)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hm) (Real.exp_ne_zero _)
  have hCancel : W x = W a * K :=
    mul_left_cancel₀ hCommon hEq
  exact (eq_div_iff (ne_of_gt hWa)).2 (by
    simpa only [mul_comm] using hCancel.symm)
