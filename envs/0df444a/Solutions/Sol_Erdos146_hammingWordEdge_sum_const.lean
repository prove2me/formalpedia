-- Prove2me | solution 1 for Erdos146.hammingWordEdge_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:35:53.547097+00:00
-- url     : https://prove2.me/submissions/fd17d6f9-42d9-4d1e-bc98-c940819184b5

import Definitions.Def_erdos146_core2
import Mathlib.InformationTheory.Hamming
import Theorems.Thm_Erdos146_hammingWordNeighbor_sum_const

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius then weight else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  simp_rw [hammingWordNeighbor_sum_const]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring
