-- Prove2me | solution 1 for ComposableDijkstraAnalysis.extraction_progress
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:26.719561+00:00
-- url     : https://prove2.me/submissions/3da8c6f3-2db4-4f2b-8438-30d9d64debdd

import Definitions.Def_Algo_dijkstra_dijkstra_Analysis


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Reusable shortest-path mathematics for Dijkstra implementations.

This module imports neither a compiled algorithm nor the Algo2Lean runtime.
Distance sequences are ordinary functions `Int → Int`. A queue backend only
needs to supply minimum selection, the relaxation scan, and exhaustion; the
path, frontier, and shortest-distance proofs are shared across backends.
-/

namespace Algo2Lean.Dijkstra

































































/-! Pure invariants for every iteration of Dijkstra, independent of the queue
implementation, storage layout, and compiler-generated transition system. -/









theorem relax_distance_other (distance : Int → Int) (target candidate vertex : Int)
    (different : vertex ≠ target) : relaxDistance distance target candidate vertex = distance vertex := by
  by_cases better : distance target < 0 ∨ candidate < distance target
  <;> simp [relaxDistance, updateDistance, better, different]































/-- The two source branches select the expected distance function. -/
theorem relax_distance_improves (distance : Int → Int) (target candidate : Int)
    (better : distance target < 0 ∨ candidate < distance target) :
    relaxDistance distance target candidate = updateDistance distance target candidate := by
  simp [relaxDistance, better]

theorem relax_distance_unchanged (distance : Int → Int) (target candidate : Int)
    (known : 0 ≤ distance target) (bounded : distance target ≤ candidate) :
    relaxDistance distance target candidate = distance := by
  have notBetter : ¬ (distance target < 0 ∨ candidate < distance target) := by omega
  simp [relaxDistance, notBetter]



/-- Settling the selected vertex freezes its own distance throughout the scan. -/
theorem RelaxScan.selected_unchanged (settled : Int → Prop) (selected : Int)
    (edges : List (Int × Int)) (distance result : Int → Int)
    (selectedSettled : settled selected) (scan : RelaxScan settled selected edges distance result) :
    result selected = distance selected := by
  induction scan with
  | empty => rfl
  | skip _ _ tail => exact tail
  | @relax target weight rest distance result unsettled _ tail =>
    rw [tail]
    exact relax_distance_other distance target (distance selected + weight) selected
      (fun same => unsettled (same ▸ selectedSettled))





/-- Mathematical scan summaries compose in the same order as source execution. -/
theorem RelaxScan.append {settled : Int → Prop} {selected : Int}
    {first second : List (Int × Int)} {before middle after : Int → Int}
    (one : RelaxScan settled selected first before middle)
    (two : RelaxScan settled selected second middle after) :
    RelaxScan settled selected (first ++ second) before after := by
  induction one with
  | empty => exact two
  | skip already _ rest => exact .skip already (rest two)
  | relax unsettled _ rest => exact .relax unsettled (rest two)











/-! Backend-independent queue and complete-loop contracts. -/



























end Algo2Lean.Dijkstra

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `dijkstra_correct`: Reusable generic Dijkstra contract.
- `dijkstra_output_exists`: Termination, shortest paths, and queue costs.
- `every_execution`: Correctness and runtime for every execution.
-/

namespace ComposableDijkstraAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.graph.Algo2LeanGenerated
open Algo.dijkstra.dijkstra
open Algo.dijkstra.priority_queue
open PriorityQueueAnalysis

/-! The graph source is imported unchanged. These finite adjacency observations
    use its public interface; all shortest-path mathematics remains shared. -/











theorem AdjacencyChain.preserved {before after : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain before size head edges)
    (unchanged : EdgeFieldsUnchanged before after) : AdjacencyChain after size head edges := by
  induction chain with
  | empty => exact .empty
  | cons edge target weight next tail valid readTarget readWeight readNext nonnegative bound weightBound chain ih =>
    obtain ⟨newValid, targetSame, weightSame, nextSame⟩ := unchanged edge valid
    exact .cons edge target weight next tail newValid (targetSame.trans readTarget)
      (weightSame.trans readWeight) (nextSame.trans readNext) nonnegative bound weightBound ih









theorem GraphFrame.refl (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef) :
    GraphFrame heap heap graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

theorem GraphFrame.trans {first middle last : Heap} {graph : Ref_Graph} {heads : CollectionRef}
    (one : GraphFrame first middle graph heads) (two : GraphFrame middle last graph heads) :
    GraphFrame first last graph heads := by
  refine ⟨fun valid => two.valid (one.valid valid), two.size.trans one.size,
    two.headsField.trans one.headsField, fun valid => two.headsValid (one.headsValid valid),
    fun vertex => (two.entries vertex).trans (one.entries vertex), ?_⟩
  intro ref valid
  obtain ⟨middleValid, firstTarget, firstWeight, firstNext⟩ := one.edges ref valid
  obtain ⟨lastValid, secondTarget, secondWeight, secondNext⟩ := two.edges ref middleValid
  exact ⟨lastValid, secondTarget.trans firstTarget, secondWeight.trans firstWeight, secondNext.trans firstNext⟩

theorem GraphRep.preserved {before after : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep before graph size heads adjacency)
    (frame : GraphFrame before after graph heads) : GraphRep after graph size heads adjacency := by
  refine ⟨frame.valid representation.valid, representation.sizeNonnegative,
    frame.size.trans representation.readSize, frame.headsField.trans representation.readHeads,
    frame.headsValid representation.headsValid, ?_⟩
  intro vertex nonnegative bound
  obtain ⟨head, readHead, chain⟩ := representation.chains vertex nonnegative bound
  exact ⟨head, (frame.entries vertex).trans readHead, chain.preserved frame.edges⟩

theorem graph_frame_write (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (ref : SeqRef) (index value : Int) : GraphFrame heap (heap.write ref index value) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩



theorem graph_frame_tick (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (clock : String) (amount : Nat) : GraphFrame heap (heap.tick clock amount) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩







variable (dependencies : Dependencies)









/-- An empty adjacency list exits the loop without changing the heap. -/
theorem scan_empty (heap : Heap) (queue : ObjectRef) (distance settled : SeqRef) (vertex : Int) :
    ScanLoop dependencies heap queue distance settled vertex none heap := by
  open Algo.dijkstra.dijkstra.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameDistance, sameSettled, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.distance, scan_edges.Local.settled,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameDistance sameSettled sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_false _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc2 _ _ caller)
    exact Reaches.single (Step.scan_edges_pc1 _ _ caller)

/-- A settled target is skipped; the loop continues at the next adjacency cell. -/
theorem scan_settled (heap finalHeap : Heap) (queue : ObjectRef) (distance settled : SeqRef)
    (vertex target : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,distance,settled,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readNext : field_Edge_next heap edge = some next)
    (already : heap.read settled target ≠ 0)
    (tail : ScanLoop dependencies (heap.tick "edges") queue distance settled vertex next finalHeap) :
    ScanLoop dependencies heap queue distance settled vertex (some edge) finalHeap := by
  open Algo.dijkstra.dijkstra.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameDistance, sameSettled, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.distance, scan_edges.Local.settled,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameDistance sameSettled sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc18 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc17_false _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using already))
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.distance,
        scan_edges.Local.settled, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller

/-- An unsettled target whose distance cannot improve leaves the queue unchanged. -/
theorem scan_unimproved (heap finalHeap : Heap) (queue : ObjectRef) (distance settled : SeqRef)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,distance,settled,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (readNext : field_Edge_next heap edge = some next)
    (unsettled : heap.read settled target = 0)
    (finite : 0 ≤ heap.read distance target)
    (notBetter : heap.read distance target ≤ heap.read distance vertex + weight)
    (tail : ScanLoop dependencies (heap.tick "edges") queue distance settled vertex next finalHeap) :
    ScanLoop dependencies heap queue distance settled vertex (some edge) finalHeap := by
  open Algo.dijkstra.dijkstra.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameDistance, sameSettled, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.distance, scan_edges.Local.settled,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameDistance sameSettled sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc18 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc17_true _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using unsettled))
    apply Reaches.prepend (Step.scan_edges_pc16 _ _ caller
      (by simpa [field__a2l_import_0_Edge_weight, readWeight] using valid.2.1))
    apply Reaches.prepend (Step.scan_edges_pc15 _ _ caller
      ⟨valid.2.1, fun _ => valid.2.1⟩)
    apply Reaches.prepend (Step.scan_edges_pc14_false _ _ caller
      (by simp [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight, readTarget, readWeight]; omega))
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.distance,
        scan_edges.Local.settled, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller

/-- A successful relaxation reuses the abstract queue Call and then resumes the loop. -/
theorem scan_improved (heap queuedHeap finalHeap : Heap) (queue : ObjectRef) (distance settled : SeqRef)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,distance,settled,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (readNext : field_Edge_next queuedHeap edge = some next)
    (unsettled : heap.read settled target = 0)
    (better : heap.read distance target < 0 ∨ heap.read distance vertex + weight < heap.read distance target)
    (update : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue
      (((heap.tick "edges").write distance target (heap.read distance vertex + weight)).tick "queue_updates")
      (queue,target,heap.read distance vertex + weight) queuedHeap ())
    (tail : ScanLoop dependencies (queuedHeap.tick "improvements") queue distance settled vertex next finalHeap) :
    ScanLoop dependencies heap queue distance settled vertex (some edge) finalHeap := by
  open Algo.dijkstra.dijkstra.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameDistance, sameSettled, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.distance, scan_edges.Local.settled,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameDistance sameSettled sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc18 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc17_true _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using unsettled))
    apply Reaches.prepend (Step.scan_edges_pc16 _ _ caller
      (by simpa [field__a2l_import_0_Edge_weight, readWeight] using valid.2.1))
    apply Reaches.prepend (Step.scan_edges_pc15 _ _ caller
      ⟨valid.2.1, fun _ => valid.2.1⟩)
    apply Reaches.prepend (Step.scan_edges_pc14_true _ _ caller
      (by simpa [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight, readTarget,readWeight] using better))
    simp only [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight,
      edge_target_tick, edge_weight_tick, readTarget, readWeight, Option.getD_some]
    apply Reaches.prepend (Step.scan_edges_pc13 _ _ caller valid.2.1)
    apply Reaches.prepend (Step.scan_edges_pc12 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc11 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc10 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue, Heap.read, Heap.tick] using update.1))
    apply Reaches.prepend (Step.scan_edges_pc9 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc8 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc7 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller update.2).trans
    apply Reaches.prepend (Step.scan_edges_pc6 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.distance,
        scan_edges.Local.settled, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller



/-- The final empty test leaves the distance reference unchanged. -/
theorem extract_empty (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef) (distance settled : SeqRef)
    (distanceAllocated : distance < heap.nextRef)
    (empty : PriorityQueue.is_empty.Call dependencies.PriorityQueue
      (heap.tick "queue_empty_checks") queue (heap.tick "queue_empty_checks") true) :
    ExtractLoop dependencies heap graph queue distance settled (heap.tick "queue_empty_checks") := by
  open Algo.dijkstra.dijkstra.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameGraph, sameQueue, sameDistance, sameSettled⟩ := located
    unfold dijkstra.At.extract at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [dijkstra.Local.graph, dijkstra.Local.queue, dijkstra.Local.distance,
      dijkstra.Local.settled] at sameGraph sameQueue sameDistance sameSettled
    subst_vars
    intro caller
    apply Reaches.prepend (Step.dijkstra_pc7 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc6 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using empty.1))
    apply Reaches.prepend (Step.dijkstra_pc5 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller empty.2).trans
    apply Reaches.prepend (Step.dijkstra_pc4 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc3_false _ _ caller rfl)
    apply Reaches.prepend (Step.dijkstra_pc2 _ _ caller)
    exact Reaches.single (Step.dijkstra_pc1 _ _ caller distanceAllocated)

/-- One extraction composes the queue contract, adjacency-loop contract, and
    next iteration. Caller frames and irrelevant locals remain encapsulated. -/
theorem extract_next (heap poppedHeap scannedHeap finalHeap : Heap)
    (graph : Ref_Graph) (queue : ObjectRef) (distance settled : SeqRef) (vertex : Int)
    (heads : CollectionRef) (head : Option Ref_Edge)
    (empty : PriorityQueue.is_empty.Call dependencies.PriorityQueue
      (heap.tick "queue_empty_checks") queue (heap.tick "queue_empty_checks") false)
    (popped : PriorityQueue.pop_min.Call dependencies.PriorityQueue
      ((heap.tick "queue_empty_checks").tick "queue_pops") queue poppedHeap vertex)
    (settledAllocated : settled < poppedHeap.nextRef)
    (readHeads : field_Graph_heads poppedHeap graph = some heads)
    (readHead : seq_Edge_optional.get poppedHeap heads vertex = some head)
    (scan : ScanLoop dependencies ((poppedHeap.write settled vertex 1).tick "settlements")
      queue distance settled vertex head scannedHeap)
    (tail : ExtractLoop dependencies scannedHeap graph queue distance settled finalHeap) :
    ExtractLoop dependencies heap graph queue distance settled finalHeap := by
  open Algo.dijkstra.dijkstra.Algo2LeanGenerated in
    have headsAfter : field__a2l_import_0_Graph_heads
        ((poppedHeap.write settled vertex 1).tick "settlements") graph = some heads := readHeads
    have headAfter : seq__a2l_import_0_Edge_optional.get
        ((poppedHeap.write settled vertex 1).tick "settlements") heads vertex = some head := readHead
    intro state located
    obtain ⟨named, sameHeap, sameGraph, sameQueue, sameDistance, sameSettled⟩ := located
    unfold dijkstra.At.extract at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [dijkstra.Local.graph, dijkstra.Local.queue, dijkstra.Local.distance,
      dijkstra.Local.settled] at sameGraph sameQueue sameDistance sameSettled
    subst_vars
    intro caller
    apply Reaches.prepend (Step.dijkstra_pc7 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc6 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using empty.1))
    apply Reaches.prepend (Step.dijkstra_pc5 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller empty.2).trans
    apply Reaches.prepend (Step.dijkstra_pc4 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.dijkstra_pc21 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc20 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc19 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using popped.1))
    apply Reaches.prepend (Step.dijkstra_pc18 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller popped.2).trans
    apply Reaches.prepend (Step.dijkstra_pc17 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc16 _ _ caller settledAllocated)
    apply Reaches.prepend (Step.dijkstra_pc15 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc14 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc13 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc12 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc11 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_pc10 _ _ caller (by simp [headsAfter,headAfter]))
    apply Reaches.prepend (Step.dijkstra_pc9 _ _ caller)
    simp only [headsAfter,headAfter,Option.getD_some]
    apply Reaches.trans (scan (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.distance,
        scan_edges.Local.settled, scan_edges.Local.vertex, scan_edges.Local.edge, Config.heap]) _)
    apply Reaches.prepend (Step.dijkstra_pc8 _ _ caller)
    exact tail (.active _ (.fn_dijkstra 7 _) [])
      (by simp [AtExtract, dijkstra.At.extract, dijkstra.Local.graph, dijkstra.Local.queue,
        dijkstra.Local.distance, dijkstra.Local.settled, Config.heap]) caller









variable {dependencies}
variable {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)



namespace QueueState






end QueueState



theorem Storage.tick {state : QueueState model} (storage : Storage model state) (name : String) :
    Storage model (state.tick model name) :=
  ⟨storage.graph.preserved (graph_frame_tick _ _ _ name 1),
    model.tick storage.queue name 1, storage.distanceAllocated,storage.settledAllocated,storage.separate⟩

theorem Storage.write {state : QueueState model} (storage : Storage model state)
    (ref : SeqRef) (index value : Int) (member : ref ∈ client.protection.sequences) :
    Storage model (state.write model ref index value) :=
  ⟨storage.graph.preserved (graph_frame_write _ _ _ ref index value),
    model.write storage.queue ref member index value,
    storage.distanceAllocated,storage.settledAllocated,storage.separate⟩

/-- The generic queue frame implies preservation of the imported graph. -/
theorem graph_frame_of_protected {before after : Heap}
    (representation : GraphRep before client.graph client.size client.heads client.adjacency)
    (frame : PriorityQueueAnalysis.Frame client.protection before after) :
    GraphFrame before after client.graph client.heads := by
  have validGraph : is_Graph after client.graph :=
    ⟨Nat.lt_of_lt_of_le representation.valid.1 frame.nextObject,
      (frame.classes _ representation.valid.1).trans representation.valid.2⟩
  have graphFields : after.objects client.graph = before.objects client.graph :=
    frame.objects _ "graph.Graph" representation.valid.1 representation.valid.2 (by simp [Client.protection])
  have graphRead : ∀ field, after.readField client.graph field = before.readField client.graph field := by
    intro field
    simp [Heap.readField,graphFields]
  have oldHeads : client.heads < before.nextCollection := representation.headsValid.1
  have headsType : after.sequenceType client.heads = before.sequenceType client.heads := frame.types _ oldHeads
  have headsValid : seq_Edge_optional.valid after client.heads :=
    ⟨Nat.lt_of_lt_of_le oldHeads frame.nextCollection, headsType.trans representation.headsValid.2⟩
  have collections := frame.collections _ (by simp [Client.protection]) oldHeads
  have entries : ∀ vertex, seq_Edge_optional.get after client.heads vertex =
      seq_Edge_optional.get before client.heads vertex := by
    intro vertex
    simp [SequenceType.get,headsValid,representation.headsValid,Heap.readElement,collections]
  refine ⟨fun _ => validGraph, ?_, ?_, fun _ => headsValid, entries, ?_⟩
  · simp [field_Graph_size, validGraph,representation.valid,graphRead]
  · simp [field_Graph_heads, validGraph,representation.valid,graphRead]
  · intro ref valid
    have newValid : is_Edge after ref :=
      ⟨Nat.lt_of_lt_of_le valid.1 frame.nextObject, (frame.classes _ valid.1).trans valid.2⟩
    have fields := frame.objects ref "graph.Edge" valid.1 valid.2 (by simp [Client.protection])
    have reads : ∀ field, after.readField ref field = before.readField ref field := by
      intro field
      simp [Heap.readField,fields]
    exact ⟨newValid, by simp [field_Edge_target,valid,newValid,reads],
      by simp [field_Edge_weight,valid,newValid,reads],
      by simp [field_Edge_next,valid,newValid,reads]⟩

theorem Storage.preserved {before after : QueueState model} (storage : Storage model before)
    (rep : model.Rep after.heap after.queueState)
    (frame : PriorityQueueAnalysis.Frame client.protection before.heap after.heap) :
    Storage model after :=
  ⟨storage.graph.preserved (graph_frame_of_protected storage.graph frame),rep,
    Nat.lt_of_lt_of_le storage.distanceAllocated frame.nextRef,
    Nat.lt_of_lt_of_le storage.settledAllocated frame.nextRef,storage.separate⟩

















variable (contracts : Contracts model reservedClocks)
include contracts

theorem work_tick_left (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model (before.tick name) after = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]

theorem work_tick_right (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model before (after.tick name) = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]





theorem queue_update (state : QueueState model) (vertex key : Int) (storage : Storage model state)
    (lower : 0 ≤ vertex) (upper : vertex < model.capacity)
    (improves : ∀ old, (vertex,old) ∈ state.entries model → key < old) :
    ∃ after, QueueUpdated model state after vertex key := by
  obtain ⟨heap,next,effect⟩ := contracts.update state.heap state.queueState vertex key storage.queue lower upper improves
  exact ⟨⟨heap,next⟩,effect.execution,storage.preserved model effect.represented effect.frame,effect.contents,
    effect.frame.sequences _ (by simp [Client.protection]) storage.distanceAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.settledAllocated,
    graph_frame_of_protected storage.graph effect.frame,effect.clocks,effect.amortized⟩

theorem queue_extract (state : QueueState model) (storage : Storage model state)
    (nonempty : state.entries model ≠ []) : ∃ after vertex key, QueueExtracted model state after vertex key := by
  obtain ⟨heap,next,vertex,key,effect⟩ := contracts.extract state.heap state.queueState storage.queue nonempty
  exact ⟨⟨heap,next⟩,vertex,key,effect.execution,storage.preserved model effect.represented effect.frame,
    effect.selected,effect.least,effect.contents,
    effect.frame.sequences _ (by simp [Client.protection]) storage.distanceAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.settledAllocated,
    graph_frame_of_protected storage.graph effect.frame,effect.clocks,effect.amortized⟩

theorem skip_edge_cost (state : QueueState model) :
    CostBounds model state (state.tick model "edges") 0 1 := by
  have zero : work model state.heap state.heap = 0 := Heap.weightedCost_self _ _
  constructor <;> try simp [QueueState.tick,Heap.cost,Heap.tick]
  change work model state.heap (state.heap.tick "edges") + _ ≤ _
  rw [work_tick_right model contracts _ _ "edges" (by simp [reservedClocks]),zero]
  simp

theorem updated_edge_cost {state after : QueueState model} {target candidate : Int}
    (effect : QueueUpdated model
      (((state.tick model "edges").write model client.distance target candidate).tick model "queue_updates")
      after target candidate) :
    CostBounds model state (after.tick model "improvements") 0 1 := by
  have clocks (name) (member : name ∈ reservedClocks) := effect.bookkeeping name member
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have same := clocks "queue_updates" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_pops" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_empty_checks" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "edges" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "improvements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "settlements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have bound := effect.amortized
    change work model (((state.heap.tick "edges").write client.distance target candidate).tick "queue_updates")
      after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "queue_updates" (by simp [reservedClocks])] at bound
    change work model (state.heap.tick "edges") after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "edges" (by simp [reservedClocks])] at bound
    change work model state.heap (after.heap.tick "improvements") + _ ≤ _
    rw [work_tick_right model contracts _ _ "improvements" (by simp [reservedClocks])]
    simpa [QueueState.tick,QueueState.write] using bound

theorem extracted_settled_cost {state after : QueueState model} {vertex key : Int}
    (effect : QueueExtracted model ((state.tick model "queue_empty_checks").tick model "queue_pops")
      after vertex key) :
    CostBounds model state ((after.write model client.settled vertex 1).tick model "settlements") 1 0 := by
  have clocks (name) (member : name ∈ reservedClocks) := effect.bookkeeping name member
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have same := clocks "queue_updates" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_pops" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_empty_checks" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "edges" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "improvements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "settlements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have bound := effect.amortized
    change work model ((state.heap.tick "queue_empty_checks").tick "queue_pops") after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "queue_pops" (by simp [reservedClocks]),
      work_tick_left model contracts _ _ "queue_empty_checks" (by simp [reservedClocks])] at bound
    change work model state.heap ((after.heap.write client.settled vertex 1).tick "settlements") + _ ≤ _
    rw [work_tick_right model contracts _ _ "settlements" (by simp [reservedClocks])]
    simpa [QueueState.tick,QueueState.write] using! bound





/-- One edge branch uses the update contract only when its candidate improves. -/
theorem advance_edge (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (selected target weight : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge)
    (storage : Storage model state) (matching : QueueMatches model state)
    (range : ∀ vertex, 0 ≤ state.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size)
    (selectedFinite : 0 ≤ state.heap.read client.distance selected)
    (validEdge : is_Edge state.heap edge)
    (readTarget : field_Edge_target state.heap edge = some target)
    (readWeight : field_Edge_weight state.heap edge = some weight)
    (readNext : field_Edge_next state.heap edge = some next)
    (targetLower : 0 ≤ target) (targetUpper : target < client.size) (weightLower : 0 ≤ weight) :
    ∃ after, EdgeAdvanced model state after selected target weight edge next := by
  have inputs : scan_edges.ValidInput dependencies state.heap
      (client.queue,client.distance,client.settled,selected,some edge) :=
    ⟨model.valid storage.queue,storage.distanceAllocated,storage.settledAllocated,
      by
        intro ref member
        have same : edge = ref := by simpa using member
        simpa only [←same] using validEdge⟩
  by_cases unsettled : state.heap.read client.settled target = 0
  · by_cases better : state.heap.read client.distance target < 0 ∨
        state.heap.read client.distance selected + weight < state.heap.read client.distance target
    · let candidate := state.heap.read client.distance selected + weight
      have candidateNonnegative : 0 ≤ candidate := by dsimp [candidate]; omega
      let prepared := ((state.tick model "edges").write model client.distance target candidate).tick model "queue_updates"
      have preparedStorage : Storage model prepared :=
        ((storage.tick model "edges").write model _ target candidate (by simp [Client.protection])).tick model "queue_updates"
      obtain ⟨after, updated⟩ := queue_update model contracts prepared target candidate preparedStorage targetLower
        (by omega) (by
          intro old member
          have key := (matching target old).mp member
          dsimp [candidate]
          omega)
      have distanceFinal : (after.tick model "improvements").heap.read client.distance =
          updateDistance (state.heap.read client.distance) target candidate := by
        rw [show (after.tick model "improvements").heap.read client.distance = after.heap.read client.distance from rfl,
          updated.distance]
        funext vertex
        simp [prepared, QueueState.tick, QueueState.write, Heap.read, Heap.write, updateDistance]
      have settledFinal : (after.tick model "improvements").heap.read client.settled =
          state.heap.read client.settled := by
        rw [show (after.tick model "improvements").heap.read client.settled = after.heap.read client.settled from rfl,
          updated.settled]
        funext vertex
        simp [prepared, QueueState.tick, QueueState.write, Heap.read, Heap.write, Ne.symm storage.separate]
      have frame : GraphFrame state.heap (after.tick model "improvements").heap client.graph client.heads :=
        (((graph_frame_tick _ _ _ "edges" 1).trans
          (graph_frame_write _ _ _ client.distance target candidate)).trans
          (graph_frame_tick _ _ _ "queue_updates" 1)).trans
          (updated.frame.trans (graph_frame_tick _ _ _ "improvements" 1))
      refine ⟨after.tick model "improvements", updated.storage.tick model "improvements", ?_, settledFinal, ?_, ?_,
        updated_edge_cost model contracts updated, frame, ?_⟩
      · intro vertex key
        change (vertex,key) ∈ after.entries model ↔ _
        rw [updated.contents, distanceFinal, settledFinal]
        change (vertex = target ∧ key = candidate) ∨ (vertex ≠ target ∧ (vertex,key) ∈ state.entries model) ↔ _
        rw [matching]
        by_cases same : vertex = target <;>
          simp [updateDistance, same, unsettled, candidateNonnegative]
      · intro vertex finite
        rw [distanceFinal] at finite
        by_cases same : vertex = target
        · simpa [same] using And.intro targetLower targetUpper
        · apply range vertex
          simpa [updateDistance, same] using finite
      · rw [distanceFinal, ← relax_distance_improves _ target candidate better]
        exact .relax (by simpa using unsettled) (.empty _)
      · intro finalHeap tail
        exact scan_improved dependencies state.heap after.heap finalHeap client.queue client.distance client.settled
          selected target weight edge next inputs readTarget readWeight
          (((frame.edges edge validEdge).2.2.2).trans readNext) unsettled better updated.execution tail
    · have finite : 0 ≤ state.heap.read client.distance target := by omega
      have noBetter : state.heap.read client.distance target ≤ state.heap.read client.distance selected + weight := by omega
      refine ⟨state.tick model "edges", storage.tick model "edges", matching, rfl, range, ?_,
        skip_edge_cost model contracts state, graph_frame_tick _ _ _ "edges" 1, ?_⟩
      · apply RelaxScan.relax (by simpa using unsettled)
        rw [relax_distance_unchanged _ target _ finite noBetter]
        exact .empty _
      · intro finalHeap tail
        exact scan_unimproved dependencies state.heap finalHeap client.queue client.distance client.settled
          selected target weight edge next inputs readTarget readWeight readNext unsettled finite noBetter tail
  · refine ⟨state.tick model "edges", storage.tick model "edges", matching, rfl, range,
      RelaxScan.skip unsettled (.empty _), skip_edge_cost model contracts state,
      graph_frame_tick _ _ _ "edges" 1, ?_⟩
    intro finalHeap tail
    exact scan_settled dependencies state.heap finalHeap client.queue client.distance client.settled
      selected target edge next inputs readTarget readNext unsettled tail

/-- Finite adjacency traversal reuses the common logical relaxation theorem. -/
theorem scan_adjacency (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (selected : Int) (head : Option Ref_Edge) (edges : List (Int × Int))
    (storage : Storage model state) (matching : QueueMatches model state)
    (range : ∀ vertex, 0 ≤ state.heap.read client.distance vertex → 0 ≤ vertex ∧ vertex < client.size)
    (selectedSettled : state.heap.read client.settled selected ≠ 0)
    (selectedFinite : 0 ≤ state.heap.read client.distance selected)
    (chain : AdjacencyChain state.heap client.size head edges) :
    ∃ after, AdjacencyScanned model state after selected head edges := by
  induction edges generalizing state head with
  | nil =>
    have empty : head = none := by cases chain; rfl
    subst head
    refine ⟨state, storage, matching, rfl, range, RelaxScan.empty _,
      CostBounds.refl model state, GraphFrame.refl _ _ _, ?_⟩
    exact scan_empty dependencies state.heap client.queue client.distance client.settled selected
  | cons pair rest ih =>
    cases chain with
    | cons edge target weight next tail valid readTarget readWeight readNext lower upper nonnegative remaining =>
      obtain ⟨middle, advanced⟩ := advance_edge model contracts capacity state selected target weight edge next
        storage matching range selectedFinite valid readTarget readWeight readNext lower upper nonnegative
      have selectedSame := RelaxScan.selected_unchanged _ selected [(target,weight)]
        (state.heap.read client.distance) (middle.heap.read client.distance) selectedSettled advanced.scan
      obtain ⟨after, scanned⟩ := ih middle next advanced.storage advanced.matching advanced.range
        (by rw [advanced.settled]; exact selectedSettled)
        (by rw [selectedSame]; exact selectedFinite) (remaining.preserved advanced.frame.edges)
      refine ⟨after, scanned.storage, scanned.matching, scanned.settled.trans advanced.settled,
        scanned.range, ?_, ?_, advanced.frame.trans scanned.frame, ?_⟩
      · have tailScan := scanned.scan
        rw [advanced.settled] at tailScan
        exact advanced.scan.append tailScan
      · simpa [Nat.add_comm] using advanced.costs.trans model scanned.costs
      · exact advanced.execution after.heap scanned.execution



theorem extraction_progress (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (remaining : List Int) (invariant : LoopInvariant model state remaining) :
    Algo2Lean.Dijkstra.Execution.Progress (executionInterface model)
      (representedEdges client.size client.adjacency) client.adjacency state remaining := by
  have emptySummary := contracts.is_empty (state.heap.tick "queue_empty_checks") state.queueState
    (model.tick invariant.storage.queue "queue_empty_checks" 1)
  by_cases empty : state.entries model = []
  · apply Algo2Lean.Dijkstra.Execution.Progress.done
    · intro vertex unsettled
      have absent := invariant.matching vertex (state.heap.read client.distance vertex)
      simp only [empty,List.not_mem_nil,false_iff,and_true] at absent
      have zero : state.heap.read client.settled vertex = 0 := by simpa [executionInterface] using unsettled
      change state.heap.read client.distance vertex < 0
      omega
    · exact ⟨extract_empty dependencies state.heap client.graph client.queue client.distance client.settled invariant.storage.distanceAllocated
        (by simpa only [show model.entries state.queueState = [] from empty, List.isEmpty_nil] using emptySummary),
        invariant.storage.distanceAllocated⟩
  · let prepared := (state.tick model "queue_empty_checks").tick model "queue_pops"
    have preparedStorage : Storage model prepared :=
      (invariant.storage.tick model "queue_empty_checks").tick model "queue_pops"
    obtain ⟨popped,vertex,key,extracted⟩ := queue_extract model contracts prepared preparedStorage empty
    have selected := (invariant.matching vertex key).mp extracted.selected
    obtain ⟨lower,upper⟩ := invariant.finiteInRange vertex selected.2.1
    have member : vertex ∈ remaining := (invariant.members vertex).mpr ⟨lower,upper,selected.1⟩
    let settled := (popped.write model client.settled vertex 1).tick model "settlements"
    have stored : Storage model settled :=
      (extracted.storage.write model _ vertex 1 (by simp [Client.protection])).tick model "settlements"
    have distanceSame : settled.heap.read client.distance = state.heap.read client.distance := by
      change (popped.heap.write client.settled vertex 1).read client.distance = _
      rw [show (popped.heap.write client.settled vertex 1).read client.distance =
          popped.heap.read client.distance by
        funext v
        exact Heap.read_write_other_ref _ _ _ _ _ _ invariant.storage.separate]
      exact extracted.distance
    have settledValues (v : Int) : settled.heap.read client.settled v =
        if v = vertex then 1 else state.heap.read client.settled v := by
      change (popped.heap.write client.settled vertex 1).read client.settled v = _
      simpa [Heap.read, Heap.write] using!
        congrArg (fun value => if v = vertex then 1 else value) (congrFun extracted.settled v)
    have matching : QueueMatches model settled := by
      intro v k
      change (v,k) ∈ popped.entries model ↔ _
      rw [extracted.contents]
      change v ≠ vertex ∧ (v,k) ∈ state.entries model ↔ _
      rw [invariant.matching,distanceSame,settledValues]
      by_cases same : v = vertex <;> simp [same]
    have settledPredicate : (fun v => settled.heap.read client.settled v ≠ 0) =
        settleVertex (fun v => state.heap.read client.settled v ≠ 0) vertex := by
      funext v
      rw [settledValues]
      apply propext
      by_cases same : v = vertex <;> simp [settleVertex,same]
    have finiteInRange : ∀ v, 0 ≤ settled.heap.read client.distance v → 0 ≤ v ∧ v < client.size := by
      rw [distanceSame]
      exact invariant.finiteInRange
    obtain ⟨head,readHead,chain⟩ := stored.graph.chains vertex lower upper
    obtain ⟨after,scanned⟩ := scan_adjacency model contracts capacity settled vertex head
      (client.adjacency vertex) stored matching finiteInRange
      (by rw [settledValues]; simp) (by rw [distanceSame]; exact selected.2.1) chain
    have next : LoopInvariant model after (remaining.erase vertex) := by
      refine ⟨scanned.storage,scanned.matching,scanned.range,invariant.unique.erase vertex,?_⟩
      intro v
      rw [invariant.unique.mem_erase_iff,invariant.members,scanned.settled,settledValues]
      by_cases same : v = vertex <;> simp [same]
    apply Algo2Lean.Dijkstra.Execution.Progress.next (after := after) (selected := vertex)
    refine ⟨member,next,?_,?_,?_,?_,?_,?_⟩
    · refine ⟨?_,selected.2.1,?_⟩
      · change ¬state.heap.read client.settled vertex ≠ 0
        simp [selected.1]
      · intro v unsettled finite
        have entry := (invariant.matching v (state.heap.read client.distance v)).mpr
          ⟨by simpa [executionInterface] using unsettled,finite,rfl⟩
        have least := extracted.least v _ entry
        simpa [selected.2.2] using! least
    · intro target weight
      simp [representedEdges,lower,upper]
    · have run := scanned.scan
      rw [distanceSame,settledPredicate] at run
      exact run
    · change (fun v => after.heap.read client.settled v ≠ 0) = _
      rw [scanned.settled,settledPredicate]
      rfl
    · intro final continuation
      refine ⟨?_,continuation.2⟩
      exact extract_next dependencies state.heap popped.heap after.heap
        (final.heap.tick "queue_empty_checks") client.graph client.queue client.distance client.settled vertex
        client.heads head (by simpa only [List.isEmpty_eq_false_iff.mpr empty] using emptySummary)
        extracted.execution extracted.storage.settledAllocated stored.graph.readHeads readHead
        scanned.execution continuation.1
    · simpa [executionInterface] using (extracted_settled_cost model contracts extracted).trans model scanned.costs











-- Main result: Correctness and running time


end ComposableDijkstraAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {dependencies : Algo.dijkstra.dijkstra.Dependencies} {client : ComposableDijkstraAnalysis.Client}
      (model : PriorityQueueAnalysis.Model dependencies.PriorityQueue client.queue client.protection),
      PriorityQueueAnalysis.Contracts model ComposableDijkstraAnalysis.reservedClocks →
        LE.le.{0} client.size model.capacity →
          ∀ (state : ComposableDijkstraAnalysis.QueueState model) (remaining : List.{0} Int),
            ComposableDijkstraAnalysis.LoopInvariant model state remaining →
              Algo2Lean.Dijkstra.Execution.Progress
                (ComposableDijkstraAnalysis.executionInterface model)
                (Algo2Lean.Dijkstra.representedEdges client.size client.adjacency) client.adjacency
                state remaining :=
  ComposableDijkstraAnalysis.extraction_progress
