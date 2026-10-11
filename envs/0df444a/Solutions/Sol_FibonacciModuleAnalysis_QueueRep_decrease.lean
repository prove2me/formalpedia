-- Prove2me | solution 1 for FibonacciModuleAnalysis.QueueRep.decrease
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:00:38.108964+00:00
-- url     : https://prove2.me/submissions/dba06e69-590d-4421-a125-d835c976bfe7

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_realize_decrease_run
import Theorems.Thm_Algo2Lean_Fibonacci_Decrease_amortized
import Theorems.Thm_Algo2Lean_Fibonacci_Represented_decrease


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
































































/-- Four units per cut allow comparisons and pointer-work event counters to
    share one potential. The resulting decrease-key charge is constant. -/
theorem Decrease.work_bound {before after : Counts} {cuts work : Nat}
    (decrease : Decrease before after cuts) (events : work ≤ 4 * cuts + 4) :
    work + scaledPotential after ≤ scaledPotential before + 20 := by
  have accounting := decrease.amortized
  simp only [scaledPotential]
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
namespace Algo2Lean.Fibonacci

















































theorem EntryChange.new_member {before after : List (Int × Int)} {vertex oldKey newKey : Int}
    (changed : EntryChange before after vertex oldKey newKey) : (vertex, newKey) ∈ after := by
  obtain ⟨unchanged, _, content⟩ := changed
  exact content.mem_iff.mpr (by simp)





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









theorem UpdateContract.cost {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (contract : UpdateContract heap after queue layout finalLayout vertex key cuts) :
    ∃ comparisons, comparisons ≤ cuts + 3 ∧ Heap.cost heap after = fun clock =>
      Clocks.single "heap_operations" 1 clock + Clocks.single "heap_cuts" cuts clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  obtain ⟨comparisons, bounded, clocks⟩ := contract.clocks
  refine ⟨comparisons, bounded, ?_⟩
  funext clock
  simp [Heap.cost, clocks clock]
  omega

/-- The cut accounting exposes a constant amount of extra work per cut. -/
theorem UpdateContract.event_work {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (contract : UpdateContract heap after queue layout finalLayout vertex key cuts) :
    heapEventWork heap after ≤ 2 * cuts + 4 := by
  obtain ⟨comparisons, bounded, equation⟩ := contract.cost
  simp [heapEventWork, equation, Clocks.single]
  omega

theorem UpdateContract.other_clocks {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (contract : UpdateContract heap after queue layout finalLayout vertex key cuts) :
    PreservesOtherClocks heap after := by
  obtain ⟨_, _, clocks⟩ := contract.clocks
  intro clock outside
  have separate : clock ≠ "heap_operations" ∧ clock ≠ "heap_cuts" ∧ clock ≠ "heap_comparisons" := by
    simp only [heapClocks, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    exact ⟨outside.1, outside.2.2.2.1, outside.2.1⟩
  simp [clocks clock, Clocks.single, separate.1, separate.2.1, separate.2.2]







end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated



/-- A single entry replacement has the expected pointwise map interface. -/
theorem QueueRep.replacement_contents {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (before : List (Int × Int)) (vertex oldKey key : Int)
    (changed : Algo2Lean.Fibonacci.EntryChange before forest.entries vertex oldKey key) :
    ∀ v k, (v, k) ∈ forest.entries ↔
      (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ before) := by
  have inserted := changed.new_member
  have newKey := (rep.represented.entry inserted).1
  obtain ⟨unchanged, beforeEntries, afterEntries⟩ := changed
  intro v k
  constructor
  · intro member
    by_cases same : v = vertex
    · subst v
      have readKey := (rep.represented.entry member).1
      exact Or.inl ⟨rfl, readKey.symm.trans newKey⟩
    · refine Or.inr ⟨same, ?_⟩
      have remaining := afterEntries.mem_iff.mp member
      simp only [List.mem_cons, Prod.mk.injEq] at remaining
      rcases remaining with ⟨impossible, _⟩ | old
      · exact False.elim (same impossible)
      · exact beforeEntries.mem_iff.mpr (by simp [old])
  · rintro (⟨rfl, rfl⟩ | ⟨different, member⟩)
    · exact inserted
    · have remaining := beforeEntries.mem_iff.mp member
      simp only [List.mem_cons, Prod.mk.injEq] at remaining
      rcases remaining with ⟨impossible, _⟩ | old
      · exact False.elim (different impossible)
      · exact afterEntries.mem_iff.mpr (by simp [old])

/-- Every strict improvement of a represented binding runs the actual compiled
    method, preserves the queue representation, and costs at most twenty
    amortized heap events. The caller sees a one-binding map update. -/
theorem QueueRep.decrease {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (present : heap.read layout.present vertex ≠ 0)
    (smaller : key < heap.read layout.keys vertex) :
    ∃ after finalLayout afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue finalLayout afterForest ∧
      (∀ v k, (v, k) ∈ afterForest.entries ↔
        (v = vertex ∧ k = key) ∨ (v ≠ vertex ∧ (v, k) ∈ forest.entries)) ∧
      heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs ∧
      PreservesOtherClocks heap after ∧
      heapEventWork heap after + Algo2Lean.Fibonacci.scaledPotential afterForest.counts ≤
        Algo2Lean.Fibonacci.scaledPotential forest.counts + 20 := by
  obtain ⟨finalSnapshot, afterForest, cuts, execution, represented, changed, accounting⟩ :=
    rep.represented.decrease vertex key present smaller
  obtain ⟨after, finalLayout, contract, observed⟩ := realize_decrease_run _ _ vertex key cuts execution
    heap queue layout rep.layoutValid rfl present
  have finalRep : QueueRep after queue finalLayout afterForest := ⟨contract.valid, by rw [observed]; exact represented⟩
  refine ⟨after, finalLayout, afterForest, contract.summary, finalRep,
    finalRep.replacement_contents _ _ _ _ changed, contract.frame, contract.refs, contract.other_clocks, ?_⟩
  apply accounting.work_bound
  have work := contract.event_work
  omega



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
          Ne.{1} (heap.read layout.present vertex) (0 : Int) →
            LT.lt.{0} key (heap.read layout.keys vertex) →
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
  FibonacciModuleAnalysis.QueueRep.decrease
