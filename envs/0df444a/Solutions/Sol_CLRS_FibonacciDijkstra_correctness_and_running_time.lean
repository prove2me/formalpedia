-- Prove2me | solution 1 for CLRS.FibonacciDijkstra.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:08:34.707542+00:00
-- url     : https://prove2.me/submissions/60cfb720-5f11-497d-bb8d-f209e6ec3c40

import Definitions.Def_SubmissionAnalysis_FibonacciDijkstra
import Theorems.Thm_FibonacciDijkstraAnalysis_summary


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
Supplemental analysis for the Algo2Lean CLRS formalization series.
This file proves a uniform-constant corollary of the exact bound;
it does not change the algorithm or its generated definitions.
-/
namespace CLRS.FibonacciDijkstra

open Algo2LeanGenerated Algo2Lean.Dijkstra



private theorem bound_le_scale (size : Int) (adjacency : Adjacency) :
    FibonacciDijkstraAnalysis.runtimeBound size adjacency ≤
      27 * runtimeScale size.toNat (edgeBudget adjacency (vertexRange size)) := by
  unfold FibonacciDijkstraAnalysis.runtimeBound runtimeScale
  have h₁ : (20 + 3) * (edgeBudget adjacency (vertexRange size) + 1) ≤
      27 * (edgeBudget adjacency (vertexRange size) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h₂ : (12 * (2 * size.toNat.log2 + 2) + 3) * size.toNat ≤
      (27 * (size.toNat.log2 + 1)) * size.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  calc
    _ ≤ 27 * (edgeBudget adjacency (vertexRange size) + 1) +
        (27 * (size.toNat.log2 + 1)) * size.toNat := Nat.add_le_add h₁ h₂
    _ = _ := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc]

/-- A single positive constant bounds every well-formed call. Correctness,
caller storage preservation, fresh output allocation and operation counts
hold for the same final heap as the running-time bound. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (graph : Algo.graph.Algo2LeanGenerated.Ref_Graph)
        (size source : Int) (heads : CollectionRef) (adjacency : Adjacency),
        ComposableDijkstraAnalysis.GraphRep heap graph size heads adjacency →
        0 ≤ source → source < size →
        ∃ after,
          Algo.dijkstra.dijkstra_fibonacci.dijkstra_fibonacci.Call
            heap (graph, source) after heap.nextRef ∧
          ComposableDijkstraAnalysis.GraphRep after graph size heads adjacency ∧
          ShortestDistances (representedEdges size adjacency) source
            (after.read heap.nextRef) ∧
          ComposableDijkstraAnalysis.OperationCounts heap after size.toNat
            (edgeBudget adjacency (vertexRange size)) ∧
          FibonacciDijkstraAnalysis.clockWork (heap.cost after) ≤
            C * runtimeScale size.toNat (edgeBudget adjacency (vertexRange size)) ∧
          heap.nextRef < after.nextRef ∧
          heap.Footprint after [] [] [] := by
  refine ⟨27, by omega, ?_⟩
  intro heap graph size source heads adjacency represented nonnegative inside
  obtain ⟨after, call, graphRep, distances, counts, cost, allocated, frame⟩ :=
    FibonacciDijkstraAnalysis.summary heap graph size source heads adjacency
      represented nonnegative inside
  exact ⟨after, call, graphRep, distances, counts,
    Nat.le_trans cost (bound_le_scale size adjacency), allocated, frame⟩

end CLRS.FibonacciDijkstra

end

set_option autoImplicit false
theorem solution :
    Exists.{1} fun C =>
      LT.lt.{0} (0 : Nat) C ∧
        ∀ (heap : Algo2LeanGenerated.Heap) (graph : Algo.graph.Algo2LeanGenerated.Ref_Graph)
          (size source : Int) (heads : Algo2LeanGenerated.CollectionRef)
          (adjacency : Algo2Lean.Dijkstra.Adjacency),
          ComposableDijkstraAnalysis.GraphRep heap graph size heads adjacency →
            LE.le.{0} (0 : Int) source →
              LT.lt.{0} source size →
                Exists.{1} fun after =>
                  Algo.dijkstra.dijkstra_fibonacci.dijkstra_fibonacci.Call heap
                      (Prod.mk.{0, 0} graph source) after heap.nextRef ∧
                    ComposableDijkstraAnalysis.GraphRep after graph size heads adjacency ∧
                      Algo2Lean.Dijkstra.ShortestDistances
                          (Algo2Lean.Dijkstra.representedEdges size adjacency) source
                          (after.read heap.nextRef) ∧
                        ComposableDijkstraAnalysis.OperationCounts heap after size.toNat
                            (Algo2Lean.Dijkstra.edgeBudget adjacency
                              (Algo2Lean.Dijkstra.vertexRange size)) ∧
                          LE.le.{0} (FibonacciDijkstraAnalysis.clockWork (heap.cost after))
                              (HMul.hMul.{0, 0, 0} C
                                (CLRS.FibonacciDijkstra.runtimeScale size.toNat
                                  (Algo2Lean.Dijkstra.edgeBudget adjacency
                                    (Algo2Lean.Dijkstra.vertexRange size)))) ∧
                            LT.lt.{0} heap.nextRef after.nextRef ∧
                              heap.Footprint after List.nil.{0} List.nil.{0} List.nil.{0} :=
  CLRS.FibonacciDijkstra.correctness_and_running_time
