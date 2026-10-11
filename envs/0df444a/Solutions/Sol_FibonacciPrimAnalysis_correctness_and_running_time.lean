-- Prove2me | solution 1 for FibonacciPrimAnalysis.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T01:20:54.472407+00:00
-- url     : https://prove2.me/submissions/0ede6ab4-442f-4925-bb86-91cb37e032a3

import Definitions.Def_Algo_prim_prim_fibonacci_Analysis
import Theorems.Thm_FibonacciPrimAnalysis_summary


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Fibonacci-heap Prim constructs three private client sequences and one queue.
    The wrapper links the generic Prim call contract to the existing Fibonacci
    heap contract, preserving the original caller's storage and clock values. -/

namespace FibonacciPrimAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim_fibonacci
open PrimGraph PrimAnalysis













/-- The explicit operational bound has one uniform constant in the conventional
    runtime scale whenever a valid root can exist. -/
theorem runtimeBound_le (size : Int) (adjacency : Adjacency) (positive : 0 < size) :
    runtimeBound size adjacency ≤ 50 * runtimeScale size adjacency := by
  have nonempty : 0 < size.toNat := by omega
  have constant : 23 ≤ 23 * size.toNat := Nat.le_mul_of_pos_right 23 nonempty
  have pops := Nat.mul_le_mul_right size.toNat
    (show (12 * (2 * size.toNat.log2 + 2) + 3) + 23 ≤
        50 * (size.toNat.log2 + 1) by omega)
  rw [Nat.add_mul] at pops
  have edges := Nat.mul_le_mul_right (edgeBudget adjacency (vertexRange size))
    (show 23 ≤ 50 by decide)
  calc
    runtimeBound size adjacency =
        23 * edgeBudget adjacency (vertexRange size) + 23 +
          (12 * (2 * size.toNat.log2 + 2) + 3) * size.toNat := by
      simp [runtimeBound, Nat.mul_add]
    _ ≤ 50 * edgeBudget adjacency (vertexRange size) +
        (50 * (size.toNat.log2 + 1)) * size.toNat := by omega
    _ = 50 * runtimeScale size adjacency := by
      unfold runtimeScale
      rw [Nat.mul_add 50 (edgeBudget adjacency (vertexRange size))]
      congr 1
      rw [Nat.mul_assoc, Nat.mul_comm (size.toNat.log2 + 1) size.toNat]





















-- Main result: Correctness and running time
/-- One uniform constant bounds the measured runtime on every represented,
    connected undirected input with a valid root. The public result remains a
    reusable Call contract, including the fresh output and caller footprint. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (graph : Ref_Graph) (size root : Int)
        (heads : CollectionRef) (adjacency : Adjacency),
        GraphRep heap graph size heads adjacency → 0 ≤ root → root < size →
        PrimGraph.Symmetric size adjacency →
        Algo2Lean.Kruskal.ConnectedOn size.toNat (inputEdges size adjacency) →
        ∃ after,
          prim_fibonacci.Call heap (graph,root) after heap.nextRef ∧
          GraphRep after graph size heads adjacency ∧
          MinimumSpanningParents size adjacency root (after.read heap.nextRef) ∧
          clockWork (Heap.cost heap after) ≤ C * runtimeScale size adjacency ∧
          heap.nextRef < after.nextRef ∧ heap.Footprint after [] [] [] := by
  refine ⟨50, by decide, ?_⟩
  intro heap graph size root heads adjacency representation rootLower rootUpper symmetric connected
  obtain ⟨after,run,graphAfter,correct,_,bound,fresh,footprint⟩ :=
    summary heap graph size root heads adjacency representation rootLower rootUpper symmetric connected
  exact ⟨after,run,graphAfter,correct,
    Nat.le_trans bound (runtimeBound_le size adjacency (by omega)),fresh,footprint⟩

end FibonacciPrimAnalysis

end

set_option autoImplicit false
theorem solution :
    Exists.{1} fun C =>
      LT.lt.{0} (0 : Nat) C ∧
        ∀ (heap : Algo2LeanGenerated.Heap) (graph : Algo.prim.graph.Algo2LeanGenerated.Ref_Graph)
          (size root : Int) (heads : Algo2LeanGenerated.CollectionRef)
          (adjacency : Algo2Lean.Dijkstra.Adjacency),
          PrimGraph.GraphRep heap graph size heads adjacency →
            LE.le.{0} (0 : Int) root →
              LT.lt.{0} root size →
                PrimGraph.Symmetric size adjacency →
                  Algo2Lean.Kruskal.ConnectedOn size.toNat (PrimGraph.inputEdges size adjacency) →
                    Exists.{1} fun after =>
                      Algo.prim.prim_fibonacci.prim_fibonacci.Call heap (Prod.mk.{0, 0} graph root)
                          after heap.nextRef ∧
                        PrimGraph.GraphRep after graph size heads adjacency ∧
                          PrimAnalysis.MinimumSpanningParents size adjacency root
                              (after.read heap.nextRef) ∧
                            LE.le.{0} (FibonacciPrimAnalysis.clockWork (heap.cost after))
                                (HMul.hMul.{0, 0, 0} C
                                  (FibonacciPrimAnalysis.runtimeScale size adjacency)) ∧
                              LT.lt.{0} heap.nextRef after.nextRef ∧
                                heap.Footprint after List.nil.{0} List.nil.{0} List.nil.{0} :=
  FibonacciPrimAnalysis.correctness_and_running_time
