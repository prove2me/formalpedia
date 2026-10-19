-- Prove2me | solution 1 for ExploreFirst.Collective.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:26:39.406519+00:00
-- url     : https://prove2.me/submissions/18f501c2-b826-403e-b1d4-dc2df080bd2b

import Mathlib

set_option autoImplicit false

theorem solution (x α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (h : (x - α) ^ 2 ≤ β * x) :
    x ≤ α + β + Real.sqrt (α * β) := by
  have hr : 0 ≤ Real.sqrt (α * β) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (α * β) ^ 2 = α * β := Real.sq_sqrt (mul_nonneg hα hβ)
  by_contra hc
  push_neg at hc
  set r := Real.sqrt (α * β) with hrdef
  have h1 : 0 < x - (α + β + r) := by linarith
  have h2 : 0 < x + (α + β + r) - (2 * α + β) := by linarith
  nlinarith [mul_pos h1 h2, mul_nonneg hβ hr]
