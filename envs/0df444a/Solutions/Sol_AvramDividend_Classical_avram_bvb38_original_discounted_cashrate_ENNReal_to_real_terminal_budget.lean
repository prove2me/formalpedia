-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb38_original_discounted_cashrate_ENNReal_to_real_terminal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:06:10.635204+00:00
-- url     : https://prove2.me/submissions/657dba9d-ae8f-4da0-b475-58bb744ce937

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (cash : ℝ≥0∞) (q m w c e : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ m) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hClock : q * c + e = 1)
    (hCash : cash ≤ ENNReal.ofReal ((q + m) * w) * ENNReal.ofReal c) :
    cash.toReal + e * w ≤ w + m * w * c  := by
  have hr : 0 ≤ (q + m) * w := mul_nonneg (add_nonneg hq hm) hw
  have hProduct : 0 ≤ ((q + m) * w) * c := mul_nonneg hr hc
  have hFinite : ENNReal.ofReal ((q + m) * w) * ENNReal.ofReal c ≠ ⊤ := by
    rw [← ENNReal.ofReal_mul hr]
    exact ENNReal.ofReal_ne_top
  have hBound := ENNReal.toReal_mono hFinite hCash
  rw [← ENNReal.ofReal_mul hr, ENNReal.toReal_ofReal hProduct] at hBound
  have hScaled := congrArg (fun z : ℝ => z * w) hClock
  nlinarith
