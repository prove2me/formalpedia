-- Prove2me | solution 1 for FamousTheorems.geom_sum_Ico
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:42:30.032068+00:00
-- url     : https://prove2.me/submissions/ea7daa12-783a-483e-bf1b-27aff3184a0d

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Real Topology EuclideanGeometry RealInnerProductSpace Affine

theorem solution {K : Type*} [DivisionRing K] {x : K} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := geom_sum_Ico hx hmn
