-- Prove2me | solution 1 for FibonacciDijkstraAnalysis.output_with_cost_correct
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:09:02.151981+00:00
-- url     : https://prove2.me/submissions/cb175321-bbd1-45ed-b611-034d20aebf04

import Definitions.Def_Algo_dijkstra_dijkstra_fibonacci_Analysis
import Theorems.Thm_FibonacciDijkstraAnalysis_summary


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The concrete wrapper constructs a queue and client arrays, then applies the
    unchanged generic Dijkstra theorem and the independent queue contract. -/

namespace FibonacciDijkstraAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.graph.Algo2LeanGenerated
open Algo.dijkstra.dijkstra_fibonacci
open ComposableDijkstraAnalysis













/-- Every completed wrapper execution has the proved result, counts, and total runtime. -/
theorem every_execution (heap after : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (result : SeqRef)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (execution : dijkstra_fibonacci.Run heap (graph,source) after result) :
    result = heap.nextRef ∧
      ShortestDistances (representedEdges size adjacency) source (after.read result) ∧
      OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      clockWork (Heap.cost heap after) ≤ runtimeBound size adjacency := by
  obtain ⟨verified,run,_,correct,counts,bound,_⟩ := summary heap graph size source heads adjacency
    representation sourceLower sourceUpper
  obtain ⟨rfl,rfl⟩ := execution.eq_of_call run
  exact ⟨rfl,correct,counts,bound⟩



-- Main result: Correctness and running time
/-- Every ordinary output has shortest distances and the total source-clock bound. -/
theorem output_with_cost_correct (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency) (output : Seq) (costs : Clocks)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (execution : dijkstra_fibonacci.ReturnsWithCost (heap,graph,source) output costs) :
    ShortestDistances (representedEdges size adjacency) source output ∧
      clockWork costs ≤ runtimeBound size adjacency := by
  obtain ⟨after,result,run,value,clocks⟩ := execution
  obtain ⟨_,correct,_,bound⟩ := every_execution heap after graph size source heads adjacency result
    representation sourceLower sourceUpper run
  change after.read result = output at value
  change Heap.cost heap after = costs at clocks
  rw [←value,←clocks]
  exact ⟨correct,bound⟩





end FibonacciDijkstraAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (graph : Algo.graph.Algo2LeanGenerated.Ref_Graph)
      (size source : Int) (heads : Algo2LeanGenerated.CollectionRef)
      (adjacency : Algo2Lean.Dijkstra.Adjacency) (output : Algo2LeanGenerated.Seq)
      (costs : Algo2LeanGenerated.Clocks),
      ComposableDijkstraAnalysis.GraphRep heap graph size heads adjacency →
        LE.le.{0} (0 : Int) source →
          LT.lt.{0} source size →
            Algo.dijkstra.dijkstra_fibonacci.dijkstra_fibonacci.ReturnsWithCost
                (Prod.mk.{0, 0} heap (Prod.mk.{0, 0} graph source)) output costs →
              Algo2Lean.Dijkstra.ShortestDistances (Algo2Lean.Dijkstra.representedEdges size adjacency)
                  source output ∧
                LE.le.{0} (FibonacciDijkstraAnalysis.clockWork costs)
                  (FibonacciDijkstraAnalysis.runtimeBound size adjacency) :=
  FibonacciDijkstraAnalysis.output_with_cost_correct
