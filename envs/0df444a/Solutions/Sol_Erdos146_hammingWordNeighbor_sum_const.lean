-- Prove2me | solution 1 for Erdos146.hammingWordNeighbor_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:35:12.015081+00:00
-- url     : https://prove2.me/submissions/0a7d8b8a-3ea8-4d28-b792-d85ba3e44d60

import Definitions.Def_erdos146_core2
import Mathlib.InformationTheory.Hamming
import Theorems.Thm_Erdos146_hammingBall_card

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension radius : ℕ) (left : HammingWord dimension)
    (weight : ℝ) :
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
      ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
        ∑ _right ∈ hammingBall dimension radius left, weight := by
          rw [← Finset.sum_filter]
          rfl
    _ = ((hammingBall dimension radius left).card : ℝ) * weight := by
      simp [nsmul_eq_mul]
    _ = ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
      rw [hammingBall_card]
