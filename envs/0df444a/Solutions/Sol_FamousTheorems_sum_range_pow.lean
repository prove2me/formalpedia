-- Prove2me | solution 1 for FamousTheorems.sum_range_pow
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:42:30.884447+00:00
-- url     : https://prove2.me/submissions/c68da54b-bcaa-4658-89fa-aa950f318260

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Real Topology EuclideanGeometry RealInnerProductSpace Affine

theorem solution (n p : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℚ) ^ p) =
      ∑ i ∈ Finset.range (p + 1),
        bernoulli i * ((p + 1).choose i) * (n : ℚ) ^ (p + 1 - i) / (p + 1) :=
  sum_range_pow n p
