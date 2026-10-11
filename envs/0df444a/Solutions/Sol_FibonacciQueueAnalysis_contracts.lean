-- Prove2me | solution 1 for FibonacciQueueAnalysis.contracts
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:04:20.953629+00:00
-- url     : https://prove2.me/submissions/4dfcf9c9-50e6-4f4e-9478-0a2787d3733b

import Definitions.Def_Algo_dijkstra_support_fibonacci_queue_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_update
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_pop_minimum


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The priority-queue contract mentions only public operations, abstract contents,
and protected client storage. A backend chooses its own ghost state and
representation. No queue layout, balancing invariant, or implementation clock
is part of this interface.
-/

namespace PriorityQueueAnalysis

open Algo2LeanGenerated
open Algo.dijkstra.priority_queue

















/-- Unique nonnegative vertex identifiers bounded by capacity give a finite queue-size bound. -/
theorem Model.cardinality_bound {code : PriorityQueue.Code} {queue : ObjectRef} {protection : Protected}
    (model : Model code queue protection) {heap : Heap} {state : model.State}
    (rep : model.Rep heap state) : (model.entries state).length ≤ model.capacity.toNat := by
  have subset_length (first second : List Int) (unique : first.Nodup)
      (subset : ∀ vertex ∈ first, vertex ∈ second) : first.length ≤ second.length := by
    induction first generalizing second with
    | nil => simp
    | cons vertex rest ih =>
      obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
      have member := subset vertex (by simp)
      have bound := ih (second.erase vertex) restUnique (by
        intro other inRest
        apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
        exact subset other (by simp [inRest]))
      have positive := List.length_pos_of_mem member
      rw [List.length_erase_of_mem member] at bound
      simp only [List.length_cons]
      omega
  have bound := subset_length ((model.entries state).map Prod.fst)
      ((List.range model.capacity.toNat).map Int.ofNat) (model.unique rep) (by
    intro vertex member
    obtain ⟨⟨v,k⟩,entry,same⟩ := List.mem_map.mp member
    obtain ⟨lower,upper⟩ := model.bounded rep v k entry
    subst vertex
    exact List.mem_map.mpr ⟨v.toNat, List.mem_range.mpr (by omega), Int.toNat_of_nonneg lower⟩)
  simpa only [List.length_map,List.length_range] using bound

end PriorityQueueAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Mathematical building blocks for Fibonacci heaps.

The tree lemmas use children in reverse link order (newest first). The rank
invariant records the consequence of equal-degree links and cutting a nonroot
when it loses its second child. The accounting relations describe actual
root/mark changes; they do not assume their amortized bounds.

This module is independent of any generated program. A compiled implementation
must separately establish the rank invariant and realize the accounting steps.
References: Fredman and Tarjan, JACM 34(3), 1987; David Karger's MIT 6.854 notes,
https://courses.csail.mit.edu/6.854/21/Notes/n01-fibonacci.html.
-/

namespace Algo2Lean.Fibonacci
































/-- Enlarging the finite size bound can only enlarge its logarithmic budget. -/
theorem log2_mono {smaller larger : Nat} (bound : smaller ≤ larger) :
    smaller.log2 ≤ larger.log2 := by
  by_cases zero : smaller = 0
  · simp [zero]
  · have positive : larger ≠ 0 := by omega
    exact (Nat.le_log2 positive).mpr (Nat.le_trans (Nat.log2_self_le zero) bound)































































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite logical forests for the mutable Fibonacci heap.

Vertex handles and keys are mathematical integers. Child lists are newest-first
in link order, matching insertion before the physical child-ring head. A ring
representation still needs to prove that its traversal realizes this finite
forest, with unique handles and the observable parent/mark/degree fields.
-/

namespace Algo2Lean.Fibonacci



























































/-- Local parent-child order implies that the root is a lower bound for every
    key in its subtree, not merely its immediate children. -/
theorem Node.Ordered.root_minimum {node : Node} (ordered : node.Ordered) :
    ∀ vertex key, (vertex, key) ∈ node.entries → node.key ≤ key := by
  induction ordered with
  | make rootBound valid ih =>
    intro vertex key member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, inside⟩
    · exact Int.le_refl _
    · exact Int.le_trans (rootBound child inChildren) (ih child inChildren vertex key inside)

/-- A minimum among the roots is a minimum among all stored vertex/key pairs. -/
theorem Forest.minimum_of_roots {forest : Forest} {minimum : Node}
    (ordered : forest.Ordered) (present : minimum ∈ forest)
    (leastRoot : ∀ root ∈ forest, minimum.key ≤ root.key) :
    (minimum.vertex, minimum.key) ∈ forest.entries ∧
      ∀ vertex key, (vertex, key) ∈ forest.entries → minimum.key ≤ key := by
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨minimum, present, ?_⟩
    cases minimum
    simp [Node.entries, Node.vertex, Node.key]
  · intro vertex key member
    obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
    exact Int.le_trans (leastRoot root inForest) ((ordered root inForest).root_minimum vertex key inside)























































































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The representation boundary between Fibonacci forests and mutable indexed storage.
Snapshots contain ordinary array observations, not a compiler configuration or a
transcript. A compiled operation must establish preservation of this relation.
-/

namespace Algo2Lean.Fibonacci











/-- Storage reads agree with every logical entry, not only the root. -/
theorem Stored.entries {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) :
    ∀ vertex key, (vertex, key) ∈ node.entries →
      state.keys vertex = key ∧ state.present vertex = 1 := by
  induction stored with
  | node key parent mark degree present childHead ring children ih =>
    intro vertex value member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, member⟩
    · exact ⟨key, present⟩
    · exact ih child inChildren vertex value member



theorem Represented.entry {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (member : (vertex, key) ∈ forest.entries) :
    state.keys vertex = key ∧ state.present vertex = 1 := by
  obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
  exact (represented.stored root inForest).entries vertex key inside



/-- The public minimum pointer identifies a present globally minimum key. -/
theorem Represented.minimum_key {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (nonempty : forest ≠ []) :
    0 ≤ state.minimum ∧ state.present state.minimum = 1 ∧
      ∀ vertex, state.present vertex ≠ 0 → state.keys state.minimum ≤ state.keys vertex := by
  rcases represented.minimum with ⟨empty, _⟩ | ⟨root, inForest, pointer, least⟩
  · exact False.elim (nonempty empty)
  obtain ⟨rootEntry, minimum⟩ := Forest.minimum_of_roots represented.valid.2.1 inForest least
  have rootValues := represented.entry rootEntry
  rw [pointer]
  refine ⟨represented.nonnegative _ _ rootEntry, rootValues.2, ?_⟩
  intro vertex present
  obtain ⟨key, member⟩ := (represented.presence vertex).mp present
  rw [rootValues.1, (represented.entry member).1]
  exact minimum vertex key member







































































































































end Algo2Lean.Fibonacci

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










theorem QueueRep.minimum {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (nonempty : forest ≠ []) :
    0 ≤ layout.minimum ∧ heap.read layout.present layout.minimum = 1 ∧
      ∀ vertex, heap.read layout.present vertex ≠ 0 →
        heap.read layout.keys layout.minimum ≤ heap.read layout.keys vertex :=
  rep.represented.minimum_key nonempty




end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

/-- Reading whether a queue is empty preserves its complete heap and clocks. -/
theorem is_empty_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) :
    FibonacciHeap.is_empty.Call heap queue heap (decide (layout.size ≤ 0)) := by
  refine ⟨valid.object, ?_⟩
  intro caller
  apply Reaches.prepend (Step.FibonacciHeap_is_empty_pc2 _ _ _ (by simp [valid.readSize]))
  simp only [valid.readSize, Option.getD_some]
  exact Reaches.single (Step.FibonacciHeap_is_empty_pc1 _ _ _)

/-- The concrete emptiness test agrees with the reusable finite entry model. -/
theorem QueueRep.is_empty {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest) :
    FibonacciHeap.is_empty.Call heap queue heap forest.entries.isEmpty := by
  have size : layout.size = (forest.entries.length : Int) := rep.represented.size
  have result : decide (layout.size ≤ 0) = forest.entries.isEmpty := by
    cases entries : forest.entries with
    | nil => simp [entries] at size; simp [size]
    | cons first rest =>
      have positive : 0 < layout.size := by rw [size, entries]; simp
      simp [show ¬ layout.size ≤ 0 by omega]
  simpa only [result] using is_empty_summary heap queue layout rep.layoutValid

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













theorem measured_work (before after : Heap) :
    Clocks.weighted metric (Heap.cost before after) = heapEventWork before after := by
  simp [metric, heapClocks, Clocks.weighted, heapEventWork, Nat.add_assoc]



/-- Local heap footprints preserve every storage class protected by the caller. -/
theorem protected_frame {before after : Heap} {queue : ObjectRef} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} {protection : Protected}
    (rep : QueueRep before queue layout forest)
    (separate : ∀ ref ∈ protection.sequences, ref ∉ layout.refs)
    (classOutside : "fibonacci_heap.FibonacciHeap" ∉ protection.objectClasses)
    (changed : before.Modifies after layout.refs [queue]) :
    PriorityQueueAnalysis.Frame protection before after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [changed.nextRef, Nat.le_refl]
  · simp only [changed.nextObject, Nat.le_refl]
  · simp only [changed.nextCollection, Nat.le_refl]
  · intro ref allocated
    exact congrFun changed.classes ref
  · intro ref allocated
    simp only [Heap.sequenceType, changed.collections]
  · intro ref guarded allocated
    exact changed.read ref (separate ref guarded)
  · intro ref className allocated tagged guarded
    apply changed.otherObjects
    simp only [List.mem_singleton]
    intro same
    subst ref
    have classNameEq : className = "fibonacci_heap.FibonacciHeap" :=
      Option.some.inj (tagged.symm.trans rep.layoutValid.object.2)
    exact classOutside (classNameEq ▸ guarded)
  · intro ref guarded allocated
    exact congrFun changed.collections ref

private theorem removed_entries {before after : Algo2Lean.Fibonacci.Forest} {vertex key : Int}
    (unique : before.Unique)
    (contents : ((vertex, key) :: after.entries).Perm before.entries) (v k : Int) :
    (v, k) ∈ after.entries ↔ v ≠ vertex ∧ (v, k) ∈ before.entries := by
  have distinct := (contents.map Prod.fst).nodup_iff.mpr unique
  have absent := (List.nodup_cons.mp distinct).1
  constructor
  · intro member
    refine ⟨?_, contents.mem_iff.mp (List.mem_cons_of_mem _ member)⟩
    intro same
    exact absent (List.mem_map.mpr ⟨(v, k), member, same⟩)
  · rintro ⟨different, member⟩
    rcases List.mem_cons.mp (contents.mem_iff.mpr member) with same | present
    · exact False.elim (different (congrArg Prod.fst same))
    · exact present

/-- All queue operations satisfy the shared interface, with the actual measured
    work and potential attached to the same execution witness. -/
theorem contracts (code : PriorityQueue.Code) (bridge : Bridge code) (queue : ObjectRef)
    (protection : Protected) (capacity : Int) (reserved : List String)
    (classOutside : "fibonacci_heap.FibonacciHeap" ∉ protection.objectClasses)
    (clockOutside : ∀ name ∈ reserved, name ∉ heapClocks) :
    Contracts (model code bridge queue protection capacity) reserved := by
  constructor
  · intro name named item included
    obtain ⟨clock, member, rfl⟩ := List.mem_map.mp included
    intro same
    exact clockOutside name named (same ▸ member)
  · intro heap state rep
    exact bridge.is_empty rep.represented.is_empty
  · intro heap state vertex key rep lower upper improvement
    obtain ⟨after, layout, forest, execution, represented, contents, changed, refs, clocks, amortized⟩ :=
      rep.represented.update vertex key lower improvement
    refine ⟨after, ⟨layout, forest⟩, bridge.update execution, ?_, contents,
      protected_frame rep.represented rep.separate classOutside changed, ?_, ?_⟩
    · refine ⟨represented, ?_, ?_,
        Heap.Footprint.trans_fresh rep.callerPreserved changed.footprint rep.privateSequences
          (by intro ref member; have same := List.mem_singleton.mp member; subst ref; exact rep.privateObject) (by simp),
        ?_, rep.privateObject, rep.clientSequences⟩
      · simpa only [refs] using rep.separate
      · intro v k member
        rcases (contents v k).mp member with ⟨rfl, rfl⟩ | ⟨_, old⟩
        · exact ⟨lower, upper⟩
        · exact rep.bounded v k old
      · simpa only [refs] using rep.privateSequences
    · intro name named
      exact clocks name (clockOutside name named)
    · simpa only [model, measured_work] using amortized
  · intro heap state rep nonempty
    have forestNonempty : state.forest ≠ [] := by
      intro empty
      exact nonempty (by simp [model, empty, Algo2Lean.Fibonacci.Forest.entries])
    obtain ⟨after, layout, forest, contract⟩ := rep.represented.pop_minimum forestNonempty
    have contents := removed_entries rep.represented.represented.valid.1 contract.contents
    refine ⟨after, ⟨layout, forest⟩, state.layout.minimum,
      heap.read state.layout.keys state.layout.minimum, bridge.extract contract.execution, ?_,
      contract.contents.mem_iff.mp (by simp), ?_, contents,
      protected_frame rep.represented rep.separate classOutside contract.frame, ?_, ?_⟩
    · refine ⟨contract.represented, ?_, ?_,
        Heap.Footprint.trans_fresh rep.callerPreserved contract.frame.footprint rep.privateSequences
          (by intro ref member; have same := List.mem_singleton.mp member; subst ref; exact rep.privateObject) (by simp),
        ?_, rep.privateObject, rep.clientSequences⟩
      · simpa only [contract.refs] using rep.separate
      · intro v k member
        exact rep.bounded v k ((contents v k).mp member).2
      · simpa only [contract.refs] using rep.privateSequences
    · intro v k member
      have stored := rep.represented.represented.entry member
      have present : heap.read state.layout.present v = 1 := stored.2
      have least := (rep.represented.minimum forestNonempty).2.2 v (by rw [present]; decide)
      have value : heap.read state.layout.keys v = k := stored.1
      simpa only [value] using least
    · intro name named
      exact contract.otherClocks name (clockOutside name named)
    · have cardinality := (model code bridge queue protection capacity).cardinality_bound rep
      have logarithm := Algo2Lean.Fibonacci.log2_mono cardinality
      have amortized := contract.amortized
      simp only [model, measured_work] at *
      omega
















end FibonacciQueueAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (code : Algo.dijkstra.priority_queue.PriorityQueue.Code)
      (bridge : FibonacciQueueAnalysis.Bridge code) (queue : Algo2LeanGenerated.ObjectRef)
      (protection : PriorityQueueAnalysis.Protected) (capacity : Int) (reserved : List.{0} String),
      ¬Membership.mem.{0, 0} protection.objectClasses "fibonacci_heap.FibonacciHeap" →
        (∀ (name : String),
            Membership.mem.{0, 0} reserved name →
              ¬Membership.mem.{0, 0} FibonacciModuleAnalysis.heapClocks name) →
          PriorityQueueAnalysis.Contracts
            (FibonacciQueueAnalysis.model code bridge queue protection capacity) reserved :=
  FibonacciQueueAnalysis.contracts
