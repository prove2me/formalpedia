-- Prove2me | solution 1 for FibonacciModuleAnalysis.QueueRep.update
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:02:11.28614+00:00
-- url     : https://prove2.me/submissions/63cc7bcf-7c00-4b71-8b22-662295909668

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_insert
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_decrease


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


































































/-- Inserting an unmarked singleton costs at most two events and deposits
    enough root credit to pay for its eventual consolidation. -/
theorem insertion_work_bound (roots marks work : Nat) (events : work ≤ 2) :
    work + scaledPotential ⟨roots + 1, marks⟩ ≤ scaledPotential ⟨roots, marks⟩ + 6 := by
  simp only [scaledPotential, potential]
  omega





























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















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis































theorem insertion_cost (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) :
    Heap.cost heap (insertionHeap heap queue layout vertex key) = fun clock =>
      Clocks.single "heap_operations" 1 clock +
        (if layout.minimum < 0 then 0 else Clocks.single "heap_comparisons" 1 clock) := by
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · funext clock
    by_cases op : clock = "heap_operations" <;>
      simp_all [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_size,
        set_FibonacciHeap_minimum, Heap.cost, Clocks.single]
  · split <;> funext clock <;> by_cases op : clock = "heap_operations" <;>
      by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [insertionHeaderHeap, rootHeaderHeap, insertRingHeap,
        set_FibonacciHeap_size, set_FibonacciHeap_minimum, Heap.cost, Clocks.single]















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

















































-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.









theorem add_root_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (clock : String) :
    (addRootHeap heap queue layout vertex).clocks clock = heap.clocks clock +
      Clocks.single "heap_comparisons" (if layout.minimum < 0 then 0 else 1) clock := by
  unfold addRootHeap
  split
  · simp_all [rootHeaderHeap, set_FibonacciHeap_minimum, Clocks.single]
  · dsimp only
    split <;> by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum, Clocks.single]














































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis





























end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

open Algo2Lean.Fibonacci.Rings



































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis



















































































theorem insertion_event_work (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : heapEventWork heap (insertionHeap heap queue layout vertex key) ≤ 2 := by
  unfold heapEventWork
  rw [insertion_cost]
  by_cases empty : layout.minimum < 0 <;> simp [empty, Clocks.single]



/-- Insertion's measured compiled work plus newly deposited potential is at
    most six. The stored forest and contents are preserved by the same run. -/
theorem QueueRep.insert_amortized {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (nonnegative : 0 ≤ vertex) (absent : heap.read layout.present vertex = 0) :
    ∃ afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
        (insertionHeap heap queue layout vertex key) () ∧
      QueueRep (insertionHeap heap queue layout vertex key) queue
        (insertionLayout heap queue layout vertex key) afterForest ∧
      afterForest.entries.Perm ((vertex, key) :: forest.entries) ∧
      heapEventWork heap (insertionHeap heap queue layout vertex key) +
        Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
          Algo2Lean.Fibonacci.scaledPotential forest.counts + 6 := by
  obtain ⟨afterForest, execution, represented, contents, roots, marks⟩ := rep.insert vertex key nonnegative absent
  refine ⟨afterForest, execution, represented, contents, ?_⟩
  have bound := Algo2Lean.Fibonacci.insertion_work_bound forest.length forest.marks
    (heapEventWork heap (insertionHeap heap queue layout vertex key))
    (insertion_event_work heap queue layout vertex key)
  simpa only [Algo2Lean.Fibonacci.Forest.counts, roots, marks] using bound



























end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis






















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis



theorem add_root_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (addRootHeap heap queue layout vertex) layout.refs [queue] := by
  unfold addRootHeap
  dsimp only
  split
  · simp only [set_FibonacciHeap_minimum, rootHeaderHeap]
    repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]
  · split <;> simp only [set_FibonacciHeap_minimum, insertRingHeap, rootHeaderHeap]
    all_goals repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField | apply Heap.Modifies.tick
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]

















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated











theorem insertion_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : heap.Modifies (insertionHeap heap queue layout vertex key) layout.refs [queue] ∧
      (insertionLayout heap queue layout vertex key).refs = layout.refs := by
  have header : heap.Modifies (insertionHeaderHeap heap queue layout vertex key) layout.refs [queue] := by
    unfold insertionHeaderHeap set_FibonacciHeap_size
    repeat' first | apply Heap.Modifies.writeField | apply Heap.Modifies.write | apply Heap.Modifies.tick
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]
  exact ⟨header.trans (add_root_frame _ _ _ _), add_root_layout_refs _ _ _⟩

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated



















/-- Insertion touches only the operation and comparison counters. -/
theorem insertion_other_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) : PreservesOtherClocks heap (insertionHeap heap queue layout vertex key) := by
  intro clock outside
  have operation : clock ≠ "heap_operations" := by
    intro same; exact outside (by simp [heapClocks, same])
  have comparison : clock ≠ "heap_comparisons" := by
    intro same; exact outside (by simp [heapClocks, same])
  unfold insertionHeap
  rw [add_root_clocks]
  simp [insertionHeaderHeap, set_FibonacciHeap_size, Heap.tick, Clocks.single, operation, comparison]

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- Fresh insertion adds exactly one binding and preserves all existing bindings. -/
theorem QueueRep.insert_contents {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest afterForest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (absent : heap.read layout.present vertex = 0)
    (entries : afterForest.entries.Perm ((vertex, key) :: forest.entries)) :
    ∀ v k, (v, k) ∈ afterForest.entries ↔
      (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ forest.entries) := by
  have unused : ∀ old, (vertex, old) ∉ forest.entries := by
    intro old member
    have present := (rep.represented.entry member).2
    change heap.read layout.present vertex = 1 at present
    omega
  intro v k
  rw [entries.mem_iff]
  simp only [List.mem_cons, Prod.mk.injEq]
  constructor
  · rintro (same | member)
    · exact Or.inl same
    · refine Or.inr ⟨?_, member⟩
      intro same
      subst v
      exact unused k member
  · rintro (same | ⟨_, member⟩)
    · exact Or.inl same
    · exact Or.inr member





/-- Push-or-decrease is a complete modular queue contract: one public call, an
    exact one-binding update, a local storage footprint, and a constant amortized
    charge. Its statement exposes no rings, degree tables, or transitions. -/
theorem QueueRep.update {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (nonnegative : 0 ≤ vertex)
    (improvement : ∀ old, (vertex, old) ∈ forest.entries → key < old) :
    ∃ after finalLayout afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue finalLayout afterForest ∧
      (∀ v k, (v, k) ∈ afterForest.entries ↔
        (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ forest.entries)) ∧
      heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs ∧
      PreservesOtherClocks heap after ∧
      heapEventWork heap after + Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
        Algo2Lean.Fibonacci.scaledPotential forest.counts + 20 := by
  by_cases absent : heap.read layout.present vertex = 0
  · obtain ⟨afterForest, execution, represented, entries, amortized⟩ := rep.insert_amortized vertex key nonnegative absent
    exact ⟨_, _, afterForest, execution, represented, rep.insert_contents vertex key absent entries,
      (insertion_frame heap queue layout vertex key).1, (insertion_frame heap queue layout vertex key).2,
      insertion_other_clocks heap queue layout vertex key, by omega⟩
  · apply rep.decrease vertex key absent
    obtain ⟨old, member⟩ := (rep.represented.presence vertex).mp absent
    have readKey := (rep.represented.entry member).1
    change heap.read layout.keys vertex = old at readKey
    rw [readKey]
    exact improvement old member

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis



























end FibonacciModuleAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {heap : Algo2LeanGenerated.Heap}
      {queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap}
      {layout : FibonacciModuleAnalysis.Layout} {forest : Algo2Lean.Fibonacci.Forest},
      FibonacciModuleAnalysis.QueueRep heap queue layout forest →
        ∀ (vertex key : Int),
          LE.le.{0} (0 : Int) vertex →
            (∀ (old : Int),
                Membership.mem.{0, 0} forest.entries (Prod.mk.{0, 0} vertex old) → LT.lt.{0} key old) →
              Exists.{1} fun after =>
                Exists.{1} fun finalLayout =>
                  Exists.{1} fun afterForest =>
                    Algo.fibonacci_heap.FibonacciHeap.push_or_decrease.Call heap
                        (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key)) after () ∧
                      FibonacciModuleAnalysis.QueueRep after queue finalLayout afterForest ∧
                        (∀ (v k : Int),
                            Membership.mem.{0, 0} afterForest.entries (Prod.mk.{0, 0} v k) ↔
                              Eq.{1} v vertex ∧ Eq.{1} k key ∨
                                Ne.{1} v vertex ∧
                                  Membership.mem.{0, 0} forest.entries (Prod.mk.{0, 0} v k)) ∧
                          heap.Modifies after layout.refs (List.cons.{0} queue List.nil.{0}) ∧
                            Eq.{1} finalLayout.refs layout.refs ∧
                              FibonacciModuleAnalysis.PreservesOtherClocks heap after ∧
                                LE.le.{0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (FibonacciModuleAnalysis.heapEventWork heap after)
                                    (Algo2Lean.Fibonacci.scaledPotential afterForest.counts))
                                  (HAdd.hAdd.{0, 0, 0}
                                    (Algo2Lean.Fibonacci.scaledPotential forest.counts) (20 : Nat)) :=
  FibonacciModuleAnalysis.QueueRep.update
