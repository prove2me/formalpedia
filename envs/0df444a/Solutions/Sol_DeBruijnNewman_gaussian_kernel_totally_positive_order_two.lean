-- Prove2me | solution 1 for DeBruijnNewman.gaussian_kernel_totally_positive_order_two
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:42:49.716981+00:00
-- url     : https://prove2.me/submissions/43e4f34e-979d-4d75-b6bb-e114400c60ee

import Mathlib

theorem solution
    (a : ℝ) (ha : 0 < a) (x1 x2 y1 y2 : ℝ)
    (hx : x1 < x2) (hy : y1 < y2) :
    0 ≤ (Matrix.of ![![Real.exp (-a * (x1 - y1) ^ 2), Real.exp (-a * (x1 - y2) ^ 2)],
          ![Real.exp (-a * (x2 - y1) ^ 2), Real.exp (-a * (x2 - y2) ^ 2)]]).det := by
  rw [Matrix.det_fin_two]
  change 0 ≤ Real.exp (-a * (x1 - y1) ^ 2) * Real.exp (-a * (x2 - y2) ^ 2) -
    Real.exp (-a * (x1 - y2) ^ 2) * Real.exp (-a * (x2 - y1) ^ 2)
  rw [← Real.exp_add, ← Real.exp_add, sub_nonneg, Real.exp_le_exp]
  nlinarith [mul_nonneg ha.le
    (mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hy.le))]
