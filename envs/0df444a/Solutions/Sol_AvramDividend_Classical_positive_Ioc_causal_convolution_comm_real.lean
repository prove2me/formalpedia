-- Prove2me | solution 1 for AvramDividend.Classical.positive_Ioc_causal_convolution_comm_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:02:34.437886+00:00
-- url     : https://prove2.me/submissions/c1a6ccef-620e-4c9e-8c09-c69898184ad3

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution (f g : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) :
    (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) =
      ∫ s in Ioc (0 : ℝ) x, g s * f (x - s) ∂volume := by
  have ha :
      (∫ s in (0 : ℝ)..x, f s * g (x - s) ∂volume) =
        (∫ s in (0 : ℝ)..x, g (x - s) * f s ∂volume) := by
    congr 1
    funext s
    ring
  have hb :
      (∫ s in (0 : ℝ)..x, g (x - s) * f s ∂volume) =
        (∫ s in (0 : ℝ)..x, g s * f (x - s) ∂volume) := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := x)
      (fun t : ℝ => g t * f (x - t)) x
    simpa only [sub_sub_cancel, sub_self, sub_zero] using h
  rw [← intervalIntegral.integral_of_le hx,
    ← intervalIntegral.integral_of_le hx]
  exact ha.trans hb
