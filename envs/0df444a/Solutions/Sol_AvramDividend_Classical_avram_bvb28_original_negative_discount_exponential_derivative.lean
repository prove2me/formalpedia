-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb28_original_negative_discount_exponential_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T11:23:26.548489+00:00
-- url     : https://prove2.me/submissions/771646c2-f7bd-4f32-9ffc-f5a1306ae613

import Mathlib

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution (q t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(q * y)))
      ((-q) * Real.exp (-(q * t))) t := by
  have hlin : HasDerivAt (fun y : ℝ => (-q) * y) (-q) t := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-q)
  have hfun : (fun y : ℝ => Real.exp (-(q * y))) = fun y => Real.exp ((-q) * y) := by
    funext y; ring_nf
  rw [hfun, show (-(q * t)) = (-q) * t by ring]
  simpa [mul_comm] using hlin.exp
