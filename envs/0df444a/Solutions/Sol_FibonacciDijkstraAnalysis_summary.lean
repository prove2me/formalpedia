-- Prove2me | solution 1 for FibonacciDijkstraAnalysis.summary
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:06:20.653114+00:00
-- url     : https://prove2.me/submissions/e048c46c-be36-47c6-8c66-f7f76b36ba95

import Definitions.Def_Algo_dijkstra_dijkstra_fibonacci_Analysis
import Theorems.Thm_ComposableDijkstraAnalysis_dijkstra_complete
import Theorems.Thm_FibonacciModuleAnalysis_new_heap_representation
import Theorems.Thm_FibonacciQueueAnalysis_contracts


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



theorem graph_frame_allocate (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (values : Seq) : GraphFrame heap (heap.allocate values) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩









variable (dependencies : Dependencies)































variable {dependencies}
variable {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)



namespace QueueState






end QueueState







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



















variable (contracts : Contracts model reservedClocks)
include contracts









































-- Main result: Correctness and running time


end ComposableDijkstraAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `new_heap_representation`: Empty Fibonacci heap representation.
- `QueueRep.update`: Insertion and decrease-key amortized contract.
- `QueueRep.pop_minimum`: Minimum extraction amortized contract.
-/

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

namespace FibonacciModuleAnalysis

-- Storage descriptions are independent of the mathematical forest invariant.
-- This lets local ring facts apply inside any caller and at any named location.




























-- Detaching a vertex changes four links and does not require a whole run.












-- Initialization follows the source allocation order. The exact-effect
-- statement can be reused without opening this method's transition rules.




theorem initialized_object (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    is_FibonacciHeap (initializedHeap heap queue) queue := by
  simpa [initializedHeap, is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid

theorem initialization_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    FibonacciHeap.__init__.Call heap queue (initializedHeap heap queue) () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap___init___pc40 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc39 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc38 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc37 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc36 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc35 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc34 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc33 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc32 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc31 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc30 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc29 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc28 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc27 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc26 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc25 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc24 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc23 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc22 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc21 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc20 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc19 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc18 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc17 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc16 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc15 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc14 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc13 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc12 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc11 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc10 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc9 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc8 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc7 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc6 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap___init___pc5 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc4 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc3 _ _ _
    (by simpa [is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid))
  apply Reaches.prepend (Step.FibonacciHeap___init___pc2 _ _ _)
  exact Reaches.single (Step.FibonacciHeap___init___pc1 _ _ _)



theorem new_heap_summary (heap : Heap) :
    FibonacciHeap.Call heap () (newHeap heap) heap.nextObject := by
  have allocated : is_FibonacciHeap (heap.allocateObject "fibonacci_heap.FibonacciHeap") heap.nextObject := by
    simp [is_FibonacciHeap]
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_pc6 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pc5 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pc4 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pc3 _ _ _)
  apply Reaches.trans ((initialization_summary _ _ allocated).2 _)
  apply Reaches.prepend (Step.FibonacciHeap_pc2 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_pc1 _ _ _ (initialized_object _ _ allocated))





































































-- A link's compiled contract is independent of any whole-heap invariant.
-- Its callers separately establish equal degree, key order, and disjoint trees.















-- The proof composes the checked ring-removal and root-insertion contracts.
-- Their internal transitions are not revisited when a cut is verified.




























-- Ranking every parent pointer is a strong sufficient termination premise.
-- The scoped parent-rank invariant restricts the ordering to active vertices, so unused
-- sequence cells can remain unconstrained. Cutting edges preserves either form.




-- A source-facing description of the cascade's exact heap changes. It records
-- actual cuts and marks, independently of the compiler's temporary states.






-- This is a terminating compiled execution, derived from decreasing parents;
-- it does not ask the caller to supply a transcript or a cascade result.















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis















































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

















































-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.
























































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis





























end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

open Algo2Lean.Fibonacci.Rings



































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis



















































































































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis






















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated













end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated





















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated









end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis



























end FibonacciModuleAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The Fibonacci implementation supplies the abstract queue contract once.
    The bridge is instantiated by generated interface-binding theorems; neither
    this module nor the heap proof imports a graph algorithm. -/

namespace FibonacciQueueAnalysis

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap
open Algo.fibonacci_heap.Algo2LeanGenerated
open Algo.dijkstra.priority_queue
open FibonacciModuleAnalysis PriorityQueueAnalysis


























private theorem constructor_old_object (heap : Heap) (ref : ObjectRef)
    (old : ref < heap.nextObject) : (newHeap heap).objects ref = heap.objects ref := by
  have different : ref ≠ heap.nextObject := Nat.ne_of_lt old
  simp [newHeap, initializedHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
    Heap.writeField, Heap.allocateObject, different]

private theorem constructor_old_sequence (heap : Heap) (ref : SeqRef)
    (old : ref < heap.nextRef) : (newHeap heap).read ref = heap.read ref := by
  have different (offset : Nat) : ref ≠ heap.nextRef + offset :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _))
  have notBase : ref ≠ heap.nextRef := Nat.ne_of_lt old
  funext index
  simp [newHeap, initializedHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
    Heap.read, Heap.allocate, Nat.add_assoc, different, notBase]

/-- Fresh construction preserves all previously allocated client storage. -/
theorem constructor_frame (heap : Heap) (protection : Protected) :
    Frame protection heap (newHeap heap) := by
  refine ⟨?_, ?_, Nat.le_refl _, ?_, fun _ _ => rfl, ?_, ?_, fun _ _ _ => rfl⟩
  · change heap.nextRef ≤ heap.nextRef + 9
    omega
  · change heap.nextObject ≤ heap.nextObject + 1
    omega
  · intro ref old
    simp only [Heap.objectClass, constructor_old_object heap ref old]
  · intro ref _ old
    exact constructor_old_sequence heap ref old
  · intro ref _ old _ _
    exact constructor_old_object heap ref old

/-- Construction changes no previously allocated caller location. -/
theorem constructor_footprint (heap : Heap) : heap.Footprint (newHeap heap) [] [] [] := by
  have frame := constructor_frame heap ⟨[], [], [], {}⟩
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.classes, frame.types,
    ?_, ?_, ?_⟩
  · intro ref old _
    exact constructor_old_sequence heap ref old
  · intro ref old _
    exact constructor_old_object heap ref old
  · intro ref old _
    rfl

theorem constructor_rep (heap : Heap) (protection : Protected) (capacity : Int)
    (allocated : ∀ ref ∈ protection.sequences, ref < heap.nextRef)
    (preserved : protection.caller.Footprint heap [] [] [])
    (clientFresh : ∀ ref ∈ protection.sequences, protection.caller.nextRef ≤ ref) :
    Rep heap.nextObject protection capacity (newHeap heap) (initialState heap) := by
  refine ⟨new_heap_representation heap, ?_, ?_, preserved.trans (constructor_footprint heap),
    ?_, preserved.nextObject, clientFresh⟩
  · intro ref member
    have old := allocated ref member
    have different (offset : Nat) : ref ≠ heap.nextRef + offset :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le old (Nat.le_add_right _ _))
    simp [initialState, emptyLayout, Layout.refs, different, Nat.ne_of_lt old]
  · intro vertex key member
    simp [initialState, Algo2Lean.Fibonacci.Forest.entries] at member

  · intro ref member
    have base := preserved.nextRef
    simp only [initialState, emptyLayout, Layout.refs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem constructor_clocks (heap : Heap) : (newHeap heap).clocks = heap.clocks := rfl

end FibonacciQueueAnalysis

end

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



/-- The wrapper's own steps only allocate its inputs and call imported code. -/
theorem call (heap queuedHeap finalHeap : Heap) (graph : Ref_Graph) (source size : Int)
    (valid : is_Graph heap graph) (readSize : field_Graph_size heap graph = some size)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size)
    (constructor : Algo.fibonacci_heap.FibonacciHeap.Call
      ((heap.allocate (fun _ => -1)).allocate (fun _ => 0)) () queuedHeap heap.nextObject)
    (search : Algo.dijkstra.dijkstra.dijkstra.Call use_dijkstra_dijkstra_0
      queuedHeap (graph,source,heap.nextObject,heap.nextRef,heap.nextRef+1) finalHeap heap.nextRef)
    (allocated : heap.nextRef < finalHeap.nextRef) :
    dijkstra_fibonacci.Call heap (graph,source) finalHeap heap.nextRef := by
  have sizeAfter : field_Graph_size (heap.allocate (fun _ => -1)) graph = some size := readSize
  open Algo.dijkstra.dijkstra_fibonacci.Algo2LeanGenerated in
    refine ⟨valid,?_⟩
    intro caller
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc19 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc18 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc17 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc16 _ _ caller (by simp [field__a2l_import_0_Graph_size,sizeAfter]))
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc15_false _ _ caller
      (by simp [field__a2l_import_0_Graph_size,sizeAfter]; omega))
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc12 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc11 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc10 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc9 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller constructor.2).trans
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc8 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc7 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc6 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc5 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc4 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc3 _ _ caller)
    apply Reaches.prepend (Step.dijkstra_fibonacci_pc2 _ _ caller)
    apply (ModuleCall.summary import_3_use_dijkstra_dijkstra_0_simulates _ caller search.2).trans
    exact Reaches.single (Step.dijkstra_fibonacci_pc1 _ _ caller allocated)







/-- A represented graph alone supplies all constructor and queue preconditions.
    The result is freshly allocated, and all pre-existing sequences, objects,
    and typed collections retain their contents. No queue-layout assumptions
    appear in this public contract. -/
theorem summary (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (representation : GraphRep heap graph size heads adjacency)
    (sourceLower : 0 ≤ source) (sourceUpper : source < size) :
    ∃ after,
      dijkstra_fibonacci.Call heap (graph,source) after heap.nextRef ∧
      GraphRep after graph size heads adjacency ∧
      ShortestDistances (representedEdges size adjacency) source (after.read heap.nextRef) ∧
      OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) ∧
      clockWork (Heap.cost heap after) ≤ runtimeBound size adjacency ∧ heap.nextRef < after.nextRef ∧
      heap.Footprint after [] [] [] := by
  let allocated := (heap.allocate (fun _ => -1)).allocate (fun _ => 0)
  let client : Client := ⟨graph,size,heads,adjacency,heap.nextRef,heap.nextRef+1,heap.nextObject,heap⟩
  let model : PriorityQueueAnalysis.Model use_dijkstra_dijkstra_0.PriorityQueue client.queue client.protection := FibonacciQueueAnalysis.model FibonacciHeap_as_PriorityQueue bridge heap.nextObject client.protection size
  let initial : QueueState (dependencies := use_dijkstra_dijkstra_0) (client := client) model := ⟨FibonacciModuleAnalysis.newHeap allocated,FibonacciQueueAnalysis.initialState allocated⟩
  have allocatedGraph : GraphRep allocated graph size heads adjacency :=
    representation.preserved ((graph_frame_allocate _ _ _ (fun _ => -1)).trans
      (graph_frame_allocate _ _ _ (fun _ => 0)))
  have protectedFrame := FibonacciQueueAnalysis.constructor_frame allocated client.protection
  have distanceAllocated : client.distance < allocated.nextRef := by
    change heap.nextRef < heap.nextRef + 1 + 1
    omega
  have settledAllocated : client.settled < allocated.nextRef := by
    change heap.nextRef + 1 < heap.nextRef + 1 + 1
    omega
  have queueRep := FibonacciQueueAnalysis.constructor_rep allocated client.protection size (by
    intro ref member
    simp only [Client.protection,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact distanceAllocated
    · exact settledAllocated)
    (((Heap.Footprint.refl heap [] [] []).allocate (fun _ => -1)).allocate (fun _ => 0)) (by
      intro ref member
      simp only [Client.protection, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [client, Client.protection])
  have storage : Storage (dependencies := use_dijkstra_dijkstra_0) (client := client) model initial := by
    refine ⟨allocatedGraph.preserved (graph_frame_of_protected allocatedGraph protectedFrame),queueRep,?_,?_,?_⟩
    · exact Nat.lt_of_lt_of_le distanceAllocated protectedFrame.nextRef
    · exact Nat.lt_of_lt_of_le settledAllocated protectedFrame.nextRef
    · simp [client]
  have distances : initial.heap.read client.distance = fun _ => -1 := by
    rw [protectedFrame.sequences client.distance (by simp [Client.protection]) distanceAllocated]
    funext vertex
    simp [client,allocated,Heap.read,Heap.allocate]
  have flags : initial.heap.read client.settled = fun _ => 0 := by
    rw [protectedFrame.sequences client.settled (by simp [Client.protection]) settledAllocated]
    funext vertex
    simp [client,allocated,Heap.read,Heap.allocate]
  have sameClocks : initial.heap.clocks = heap.clocks :=
    FibonacciQueueAnalysis.constructor_clocks allocated
  have contracts : PriorityQueueAnalysis.Contracts model reservedClocks :=
    FibonacciQueueAnalysis.contracts FibonacciHeap_as_PriorityQueue bridge heap.nextObject client.protection size reservedClocks
      (by simp [Client.protection]) (by intro name member; simp [reservedClocks] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨after,search,graphAfter,correct,counts,workBound,resultAllocated,preserved⟩ :=
    dijkstra_complete model contracts (Int.le_refl _) initial source storage (by rfl) distances flags sourceLower sourceUpper
  have sameCost : Heap.cost initial.heap after = Heap.cost heap after := by
    funext name
    simp only [Heap.cost,sameClocks]
  have costs : OperationCounts heap after size.toNat (edgeBudget adjacency (vertexRange size)) := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa only [sameCost] using counts.updates
    · simpa only [sameCost] using counts.pops
    · simpa only [sameCost] using counts.checks
    · simpa only [sameCost] using counts.visits
    · simpa only [sameCost] using counts.improvements
    · simpa only [sameCost] using counts.settlements
  refine ⟨after,call heap initial.heap after graph source size representation.valid representation.readSize
    sourceLower sourceUpper (FibonacciModuleAnalysis.new_heap_summary allocated) search resultAllocated,
    graphAfter,correct,costs,?_,resultAllocated,preserved⟩
  have updates := costs.updates
  have pops := costs.pops
  have checks := costs.checks
  have edges := costs.visits
  have improvements := costs.improvements
  have settlements := costs.settlements
  change Clocks.weighted model.metric (Heap.cost initial.heap after) ≤ _ at workBound
  rw [sameCost] at workBound
  simp [client,model,FibonacciQueueAnalysis.model,QueueState.potential,initial,FibonacciQueueAnalysis.initialState,Algo2Lean.Fibonacci.scaledPotential,Algo2Lean.Fibonacci.potential,Algo2Lean.Fibonacci.Forest.counts,Algo2Lean.Fibonacci.Forest.marks] at workBound
  simp only [clockWork,runtimeBound,Nat.add_mul,Nat.mul_add,Nat.mul_one] at workBound ⊢
  omega





-- Main result: Correctness and running time






end FibonacciDijkstraAnalysis

end

set_option autoImplicit false
theorem solution :
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
                          (FibonacciDijkstraAnalysis.runtimeBound size adjacency) ∧
                        LT.lt.{0} heap.nextRef after.nextRef ∧
                          heap.Footprint after List.nil.{0} List.nil.{0} List.nil.{0} :=
  FibonacciDijkstraAnalysis.summary
