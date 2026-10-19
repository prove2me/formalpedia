-- Prove2me | solution 1 for CLRS.HeapSortIndices.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:16:16.236515+00:00
-- url     : https://prove2.me/submissions/41fa9b57-b78b-48e2-8016-435ae27998f9

import Mathlib.Tactic.Linarith
import Theorems.Thm_SortIndicesAnalysis_call

set_option autoImplicit false

open Algo2LeanGenerated

theorem solution :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (keys : SeqRef) (n : Nat), keys < heap.nextRef →
        ∃ after result,
          Algo.sort_indices.sort_indices.Call heap (keys, (n : Int)) after result ∧
          SortIndicesAnalysis.SortedPermutation (heap.read keys) (n : Int) (after.read result) ∧
          SortIndicesAnalysis.Preserves heap after ∧
          heap.nextRef ≤ result ∧ result < after.nextRef ∧
          SortIndicesAnalysis.Budget (n : Int) (2 * n) heap after ∧
          SortIndicesAnalysis.runtime (Heap.cost heap after) ≤
            C * (1 + n * (1 + Nat.log2 (n + 1))) := by
  refine ⟨6, by decide, ?_⟩
  intro heap keys n allocated
  obtain ⟨after, result, run, sorted, preserved, fresh, valid, budget⟩ :=
    SortIndicesAnalysis.call heap keys (n : Int) allocated (Int.natCast_nonneg n)
  have budget' : SortIndicesAnalysis.Budget (n : Int) (2 * n) heap after := by
    simpa using budget
  refine ⟨after, result, run, sorted, preserved, fresh, valid, budget', ?_⟩
  have steps := budget' "sort_steps"
  have comparisons := budget' "heap_comparisons"
  have swaps := budget' "heap_swaps"
  simp [SortIndicesAnalysis.rate, BinaryModuleAnalysis.depth] at steps comparisons swaps
  have hs : Heap.cost heap after "sort_steps" ≤ 2 * n := by
    simp only [Heap.cost]
    omega
  have hc : Heap.cost heap after "heap_comparisons" ≤ 2 * n * (2 * Nat.log2 (n + 1)) := by
    simp only [Heap.cost]
    omega
  have hw : Heap.cost heap after "heap_swaps" ≤ 2 * n * (Nat.log2 (n + 1) + 1) := by
    simp only [Heap.cost]
    omega
  simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_mul, Nat.add_zero]
  nlinarith
