-- Prove2me | solution 1 for Erdos146.hammingWordEdgePairSharedLeft_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:36:34.99042+00:00
-- url     : https://prove2.me/submissions/fff6fdb0-83e7-4a24-9300-e0a9a3bb7857

import Definitions.Def_erdos146_core2
import Mathlib.InformationTheory.Hamming
import Theorems.Thm_Erdos146_hammingWordEdge_sum_const
import Theorems.Thm_Erdos146_hammingWordNeighbor_sum_const

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  have hshared (firstLeft : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
    calc
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        ∑ secondLeft : HammingWord dimension,
          if firstLeft = secondLeft then
            ∑ secondRight : HammingWord dimension,
              if hammingDist secondLeft secondRight ≤ radius then
                weight else 0
          else 0 := by
            apply Finset.sum_congr rfl
            intro secondLeft _
            by_cases hleft : firstLeft = secondLeft
            · subst secondLeft
              simp
            · simp [hleft]
      _ = ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) * weight := by
        simp [hammingWordNeighbor_sum_const]
  have hinner (firstLeft firstRight : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        if hammingDist firstLeft firstRight ≤ radius then
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) * weight
        else 0 := by
    by_cases hedge : hammingDist firstLeft firstRight ≤ radius
    · simp only [hedge, true_and, if_true]
      exact hshared firstLeft
    · simp [hedge]
  simp_rw [hinner]
  rw [hammingWordEdge_sum_const]
  ring
