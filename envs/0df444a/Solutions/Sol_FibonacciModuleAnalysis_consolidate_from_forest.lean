-- Prove2me | solution 1 for FibonacciModuleAnalysis.consolidate_from_forest
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:52.062995+00:00
-- url     : https://prove2.me/submissions/93ba7c9d-b99b-4756-83d9-eb5ada4a60ac

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_add_root_summary
import Theorems.Thm_FibonacciModuleAnalysis_link_summary
import Theorems.Thm_FibonacciModuleAnalysis_realize_root_consumption
import Theorems.Thm_Algo2Lean_Fibonacci_SplitRepresented_consume_roots


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
















































































/-- No-duplicate degree buckets fit inside the finite range `0..maximum`. -/
theorem distinct_degrees_bound (degrees : List Nat) (maximum : Nat)
    (unique : degrees.Nodup) (bounded : ∀ degree ∈ degrees, degree ≤ maximum) :
    degrees.length ≤ maximum + 1 := by
  have subsetLength : ∀ first second : List Nat, first.Nodup →
      (∀ value ∈ first, value ∈ second) → first.length ≤ second.length := by
    intro first
    induction first with
    | nil => intro second unique contained; simp
    | cons value rest ih =>
      intro second unique contained
      obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
      have member := contained value (by simp)
      have tailBound := ih (second.erase value) restUnique (by
        intro other inRest
        apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
        exact contained other (by simp [inRest]))
      have length := List.length_erase_of_mem member
      have positive := List.length_pos_of_mem member
      simp only [List.length_cons]
      omega
  have bound := subsetLength degrees (List.range (maximum + 1)) unique (by
    intro degree member
    exact List.mem_range.mpr (by have := bounded degree member; omega))
  simpa using bound















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





































































































/-- Content permutations preserve handle uniqueness; no pointer or key
    identity is lost during structural forest operations. -/
theorem Forest.Unique.of_entries_perm {before after : Forest} (unique : before.Unique)
    (contents : after.entries.Perm before.entries) : after.Unique :=
  ((contents.map Prod.fst).nodup_iff).mpr unique















































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite circular doubly linked lists for Fibonacci-heap pointer proofs.

The representation is independent of heaps and sequence references: `left` and
`right` are the integer-indexed pointer arrays observed through an allocated
sequence. Primitive effects below follow the source's precise write order.
-/

namespace Algo2Lean.Fibonacci.Rings













theorem Chain.first_mem {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : first ∈ vertices := by
  cases chain <;> simp

theorem Chain.last_mem {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : last ∈ vertices := by
  induction chain with
  | singleton => simp
  | cons first _ _ _ ih => simp [ih]

theorem Chain.head {left right : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) : ∃ tail, vertices = first :: tail := by
  cases chain <;> exact ⟨_, rfl⟩



/-- Open chains can be joined at one new edge. -/
theorem Chain.append {left right : Int → Int} {first middle next last : Int}
    {front back : List Int} (one : Chain left right first front middle)
    (two : Chain left right next back last) (forward : right middle = next)
    (backward : left next = middle) : Chain left right first (front ++ back) last := by
  induction one with
  | singleton => exact .cons _ forward backward two
  | cons first rightFirst leftNext tail ih => exact .cons first rightFirst leftNext (ih forward backward)

/-- Pointer updates at a chain's external endpoints do not affect its
    internal links. All other observations only need agree on this chain. -/
theorem Chain.frame {left right newLeft newRight : Int → Int} {first last : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) (unique : vertices.Nodup)
    (leftSame : ∀ vertex ∈ vertices, vertex ≠ first → newLeft vertex = left vertex)
    (rightSame : ∀ vertex ∈ vertices, vertex ≠ last → newRight vertex = right vertex) :
    Chain newLeft newRight first vertices last := by
  induction chain with
  | singleton => exact .singleton _
  | @cons first next last tail forward backward chain ih =>
    obtain ⟨firstAbsent, tailUnique⟩ := List.nodup_cons.mp unique
    have firstLast : first ≠ last := by intro same; exact firstAbsent (same.symm ▸ chain.last_mem)
    have nextFirst : next ≠ first := by intro same; exact firstAbsent (same ▸ chain.first_mem)
    refine Chain.cons first (next := next) ?_ ?_ ?_
    · rw [rightSame first (by simp) firstLast]
      exact forward
    · rw [leftSame next (by simp [chain.first_mem]) nextFirst]
      exact backward
    · apply ih tailUnique
      · intro vertex member _
        apply leftSame vertex (by simp [member])
        intro same
        subst vertex
        exact firstAbsent member
      · intro vertex member different
        exact rightSame vertex (by simp [member]) different

/-- Equal pointer values on ring members preserve the ring; other array entries
    may differ. -/
theorem Ring.frame {left right newLeft newRight : Int → Int} {vertices : List Int}
    (ring : Ring left right vertices)
    (leftSame : ∀ vertex ∈ vertices, newLeft vertex = left vertex)
    (rightSame : ∀ vertex ∈ vertices, newRight vertex = right vertex) :
    Ring newLeft newRight vertices := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  refine ⟨ring.unique, first, last, chain.frame ring.unique (fun v member _ => leftSame v member)
    (fun v member _ => rightSame v member), ?_, ?_⟩
  · rw [rightSame last chain.last_mem]
    exact forward
  · rw [leftSame first chain.first_mem]
    exact backward

/-- Every pointer read at a ring member stays within that finite ring. -/
theorem Chain.neighbors {left right : Int → Int} {first last vertex : Int} {vertices : List Int}
    (chain : Chain left right first vertices last) (member : vertex ∈ vertices) :
    (vertex = first ∨ left vertex ∈ vertices) ∧ (vertex = last ∨ right vertex ∈ vertices) := by
  induction chain with
  | singleton =>
    have same := List.mem_singleton.mp member
    exact ⟨Or.inl same, Or.inl same⟩
  | @cons first next last tail forward backward chain ih =>
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨Or.inl rfl, Or.inr (by rw [forward]; simp [chain.first_mem])⟩
    · obtain ⟨leftNeighbor, rightNeighbor⟩ := ih inTail
      constructor
      · rcases leftNeighbor with rfl | inside
        · exact Or.inr (by rw [backward]; simp)
        · exact Or.inr (by simp [inside])
      · rcases rightNeighbor with same | inside
        · exact Or.inl same
        · exact Or.inr (by simp [inside])

theorem Ring.neighbors {left right : Int → Int} {vertex : Int} {vertices : List Int}
    (ring : Ring left right vertices) (member : vertex ∈ vertices) :
    left vertex ∈ vertices ∧ right vertex ∈ vertices := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  obtain ⟨leftNeighbor, rightNeighbor⟩ := chain.neighbors member
  constructor
  · rcases leftNeighbor with rfl | inside
    · rw [backward]; exact chain.last_mem
    · exact inside
  · rcases rightNeighbor with rfl | inside
    · rw [forward]; exact chain.first_mem
    · exact inside

/-- A displayed list head is the first endpoint of its open chain. -/
theorem Ring.open_head {left right : Int → Int} {head : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) :
    ∃ last, Chain left right head (head :: tail) last ∧ right last = head ∧ left head = last := by
  obtain ⟨first, last, chain, forward, backward⟩ := ring.closed
  obtain ⟨rest, same⟩ := chain.head
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  exact ⟨last, chain, forward, backward⟩









theorem singleton_ring (left right : Int → Int) (vertex : Int)
    (selfLeft : left vertex = vertex) (selfRight : right vertex = vertex) : Ring left right [vertex] :=
  ⟨by simp, vertex, vertex, Chain.singleton vertex, selfRight, selfLeft⟩

/-- Inserting a fresh vertex before the chosen head realizes list prepend.
    The inserted vertex's previous pointers need not already be self-links. -/
theorem Ring.insert_before {left right : Int → Int} {head vertex : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) (fresh : vertex ∉ head :: tail) :
    Ring (insertBeforeLeft left head vertex) (insertBeforeRight left right head vertex)
      (vertex :: head :: tail) := by
  obtain ⟨last, chain, closesRight, closesLeft⟩ := ring.open_head
  have vertexHead : vertex ≠ head := by intro same; exact fresh (by simp [same])
  have oldDifferent (other : Int) (member : other ∈ head :: tail) : other ≠ vertex := by
    intro same
    exact fresh (same ▸ member)
  have vertexLast : vertex ≠ last := Ne.symm (oldDifferent last chain.last_mem)
  have inside : Chain (insertBeforeLeft left head vertex) (insertBeforeRight left right head vertex)
      head (head :: tail) last := by
    apply chain.frame ring.unique
    · intro other member notHead
      simp [insertBeforeLeft, write, oldDifferent other member, notHead]
    · intro other member notLast
      simp [insertBeforeRight, write, closesLeft, oldDifferent other member, notLast]
  refine ⟨List.nodup_cons.mpr ⟨fresh, ring.unique⟩, vertex, last,
    Chain.cons vertex (next := head) ?_ ?_ inside, ?_, ?_⟩
  · simp [insertBeforeRight, write, closesLeft, vertexLast]
  · simp [insertBeforeLeft, write]
  · simp [insertBeforeRight, write, closesLeft]
  · simp [insertBeforeLeft, write, closesLeft, vertexHead]





/-- Choosing the next node as the head rotates the list but changes no pointers. -/
theorem Ring.rotate_head {left right : Int → Int} {head : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) : Ring left right (tail ++ [head]) := by
  obtain ⟨last, chain, forward, backward⟩ := ring.open_head
  have unique : (tail ++ [head]).Nodup := by
    exact (List.perm_append_comm (l₁ := tail) (l₂ := [head])).nodup_iff.mpr ring.unique
  cases chain with
  | singleton => exact ring
  | @cons first next last tail rightHead leftNext rest =>
    exact ⟨unique, next, head, rest.append (.singleton head) forward backward, rightHead, leftNext⟩

/-- Any cyclic rotation describes the same ring. -/
theorem Ring.rotate_append {left right : Int → Int} (front back : List Int)
    (ring : Ring left right (front ++ back)) : Ring left right (back ++ front) := by
  induction front generalizing back with
  | nil => simpa using ring
  | cons head front ih =>
    have rotated := ring.rotate_head
    change Ring left right ((front ++ back) ++ [head]) at rotated
    have nextRing : Ring left right (front ++ (back ++ [head])) := by
      simpa only [List.append_assoc] using rotated
    have final := ih (back ++ [head]) nextRing
    simpa only [List.append_assoc, List.singleton_append] using final

theorem RingOrEmpty.rotate_append {left right : Int → Int} (front back : List Int)
    (ring : RingOrEmpty left right (front ++ back)) : RingOrEmpty left right (back ++ front) := by
  rcases ring with empty | ring
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp empty
    exact Or.inl rfl
  · exact Or.inr (ring.rotate_append front back)









theorem Ring.singleton_pointers {left right : Int → Int} {vertex : Int}
    (ring : Ring left right [vertex]) : left vertex = vertex ∧ right vertex = vertex := by
  obtain ⟨last, chain, forward, backward⟩ := ring.open_head
  cases chain with
  | singleton => exact ⟨backward, forward⟩
  | cons _ _ _ rest => cases rest

theorem Ring.head_next {left right : Int → Int} {head next : Int} {tail : List Int}
    (ring : Ring left right (head :: next :: tail)) : right head = next ∧ left next = head := by
  obtain ⟨last, chain, _, _⟩ := ring.open_head
  cases chain with
  | @cons _ child _ _ forward backward rest =>
    obtain ⟨remaining, same⟩ := rest.head
    obtain ⟨rfl, rfl⟩ := List.cons.inj same
    exact ⟨forward, backward⟩





/-- Insertion after a representative is insertion before its successor, so
    the resulting ring order is `head :: vertex :: tail`. -/
theorem Ring.insert_after {left right : Int → Int} {head vertex : Int} {tail : List Int}
    (ring : Ring left right (head :: tail)) (fresh : vertex ∉ head :: tail) :
    Ring (insertAfterLeft left right head vertex) (insertAfterRight right head vertex)
      (head :: vertex :: tail) := by
  cases tail with
  | nil =>
    obtain ⟨selfLeft, selfRight⟩ := ring.singleton_pointers
    have result := (ring.insert_before fresh).rotate_head
    simpa [insertBeforeLeft, insertBeforeRight, insertAfterLeft, insertAfterRight, selfLeft, selfRight] using result
  | cons next rest =>
    obtain ⟨forward, backward⟩ := ring.head_next
    have rotated : Ring left right (next :: (rest ++ [head])) := ring.rotate_head
    have freshRotated : vertex ∉ next :: (rest ++ [head]) := by
      simpa [or_comm, or_left_comm, or_assoc] using fresh
    have inserted := rotated.insert_before freshRotated
    have restored := inserted.rotate_append (vertex :: next :: rest) [head]
    simpa only [List.singleton_append, insertBeforeLeft, insertBeforeRight,
      insertAfterLeft, insertAfterRight, forward, backward] using restored



end Algo2Lean.Fibonacci.Rings

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





theorem Stored.root_key {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.keys node.vertex = node.key := by
  cases stored
  assumption





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





















theorem Node.child_entries {node child : Node} (childMember : child ∈ node.children)
    {vertex key : Int} (inside : (vertex, key) ∈ child.entries) : (vertex, key) ∈ node.entries := by
  cases node
  simp only [Node.children] at childMember
  simp only [Node.entries, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨child, childMember, inside⟩

theorem Node.descendant_entries {node : Node} {vertex key : Int}
    (member : (vertex, key) ∈ node.children.flatMap Node.entries) : (vertex, key) ∈ node.entries := by
  obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
  exact Node.child_entries childMember inside

theorem Stored.root_parent {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.parents node.vertex = parent := by
  cases stored
  assumption

/-- A stored subtree can be reused when its metadata and its descendants'
    sibling pointers are preserved. The root's own sibling pointers are irrelevant. -/
theorem Stored.frame {before after : Snapshot} {parent : Int} {node : Node}
    (stored : Stored before parent node)
    (fields : ∀ vertex key, (vertex, key) ∈ node.entries → Snapshot.SameFields before after vertex)
    (links : ∀ vertex key, (vertex, key) ∈ node.children.flatMap Node.entries →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after parent node := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    have rootFields := fields vertex key (by simp [Node.entries])
    refine Stored.node (rootFields.key.trans readKey) (rootFields.parent.trans readParent)
      (rootFields.mark.trans readMark) (rootFields.degree.trans readDegree)
      (rootFields.present.trans readPresent)
      (by cases children <;> exact rootFields.child.trans readChild) ?_ ?_
    · rcases ring with empty | ring
      · exact Or.inl empty
      · apply Or.inr
        apply ring.frame
        · intro value member
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).1
        · intro value member
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
          exact (links child.vertex child.key (List.mem_flatMap.mpr ⟨child, childMember, child.root_entry⟩)).2
    · intro child member
      apply ih child member
      · intro vertex key inside
        apply fields vertex key
        exact Node.child_entries member inside
      · intro vertex key inside
        apply links vertex key
        exact List.mem_flatMap.mpr ⟨child, member, Node.descendant_entries inside⟩

/-- Nonroot entries have nonnegative parent handles. This lets root-ring
    rewiring be separated from every stored subtree's internal child rings. -/
theorem Stored.parents_nonnegative {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) (parentNonnegative : 0 ≤ parent)
    (verticesNonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex) :
    ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ state.parents vertex := by
  induction stored with
  | @node vertex key parent marked children readKey readParent readMark readDegree readPresent readChild ring subtrees ih =>
    intro value weight member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, childMember, inside⟩
    · simpa only [readParent] using parentNonnegative
    · apply ih child childMember _ _ value weight inside
      · exact verticesNonnegative vertex key (by simp [Node.entries])
      · intro descendant descendantKey descendantMember
        exact verticesNonnegative descendant descendantKey (Node.child_entries childMember descendantMember)

/-- Preserving all active nonroot pointers suffices to preserve each old tree
    when only root-ring links and previously absent array cells are changed. -/
theorem Stored.frame_roots {before after : Snapshot} {parent : Int} {node : Node}
    (stored : Stored before parent node)
    (nonnegative : ∀ vertex key, (vertex, key) ∈ node.entries → 0 ≤ vertex)
    (fields : ∀ vertex key, (vertex, key) ∈ node.entries → Snapshot.SameFields before after vertex)
    (links : ∀ vertex, before.present vertex = 1 → 0 ≤ before.parents vertex →
      after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex) :
    Stored after parent node := by
  apply stored.frame fields
  intro vertex key member
  obtain ⟨child, childMember, inside⟩ := List.mem_flatMap.mp member
  have childrenStored : ∀ child ∈ node.children, Stored before node.vertex child := by
    cases stored with | node _ _ _ _ _ _ _ children => exact children
  have childStored := childrenStored child childMember
  apply links vertex ((childStored.entries vertex key inside).2)
  exact childStored.parents_nonnegative (nonnegative node.vertex node.key node.root_entry)
    (fun value weight inside => nonnegative value weight (Node.child_entries childMember inside)) vertex key inside


/-- Reordering roots changes neither heap order nor the rank history inside a tree. -/
theorem Forest.Valid.perm {before after : Forest} (valid : before.Valid)
    (permutation : after.Perm before) : after.Valid := by
  refine ⟨valid.1.of_entries_perm (permutation.flatMap_right Node.entries), ?_, ?_, ?_⟩
  · intro root member
    exact valid.2.1 root (permutation.mem_iff.mp member)
  · intro root member
    exact valid.2.2.1 root (permutation.mem_iff.mp member)
  · intro root member
    exact valid.2.2.2 root (permutation.mem_iff.mp member)






























/-- The two parts of a unique forest have disjoint addresses. This is the
    separation fact needed when a root is detached and later linked. -/
theorem Forest.Unique.disjoint {front back : Forest} (unique : Forest.Unique (front ++ back)) :
    ∀ vertex, front.Has vertex → ¬back.Has vertex := by
  unfold Forest.Unique at unique
  simp only [Forest.entries, List.flatMap_append, List.map_append] at unique
  have separate := (List.nodup_append.mp unique).2.2
  intro vertex inFront inBack
  exact separate vertex ((front.has_iff_map vertex).mp inFront)
    vertex ((back.has_iff_map vertex).mp inBack) rfl







/-- A root-ring vertex cannot be an entry in a separate forest component. -/
theorem Forest.Unique.roots_disjoint {front back : Forest}
    (unique : Forest.Unique (front ++ back)) :
    ∀ vertex ∈ front.map Node.vertex, vertex ∉ back.entries.map Prod.fst := by
  intro vertex member inside
  obtain ⟨root, member, same⟩ := List.mem_map.mp member
  exact unique.disjoint vertex
    ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
    ((back.has_iff_map vertex).mpr inside)





































































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci











/-- The detached list is ghost bookkeeping: all its roots have self-rings. -/
theorem SplitRepresented.perm_detached {state : Snapshot} {pending before after : Forest}
    (represented : SplitRepresented state pending before) (permutation : after.Perm before) :
    SplitRepresented state pending after := by
  have whole := permutation.append_left pending
  have contents := whole.flatMap_right Node.entries
  refine ⟨represented.valid.perm whole, ?_, represented.pendingRing, ?_, ?_, ?_, ?_, represented.cursor⟩
  · intro root member
    exact represented.stored root (whole.mem_iff.mp member)
  · intro root member
    exact represented.detachedRings root (permutation.mem_iff.mp member)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)

/-- Pending root lists may be rotated to expose the actual cursor. -/
theorem SplitRepresented.rotate_pending {state : Snapshot} {front back detached : Forest}
    (represented : SplitRepresented state (front ++ back) detached) :
    SplitRepresented state (back ++ front) detached := by
  have rotation : (back ++ front).Perm (front ++ back) := List.perm_append_comm
  have whole := rotation.append_right detached
  have contents := whole.flatMap_right Node.entries
  refine ⟨represented.valid.perm whole, ?_, ?_, represented.detachedRings, ?_, ?_, ?_, ?_⟩
  · intro root member
    exact represented.stored root (whole.mem_iff.mp member)
  · simpa only [List.map_append] using Rings.RingOrEmpty.rotate_append
      (front.map Node.vertex) (back.map Node.vertex) (by simpa only [List.map_append] using represented.pendingRing)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · rcases represented.cursor with ⟨empty, pointer⟩ | ⟨root, member, pointer⟩
    · left
      exact ⟨by simpa only [List.append_eq_nil_iff, and_comm] using empty, pointer⟩
    · exact Or.inr ⟨root, rotation.mem_iff.mpr member, pointer⟩

/-- Updating scratch buckets changes no represented node or pending pointer. -/
theorem SplitRepresented.table_write {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (degree vertex : Int) :
    SplitRepresented {state with table := Rings.write state.table degree vertex} pending detached := by
  refine ⟨represented.valid, ?_, represented.pendingRing, represented.detachedRings,
    represented.nonnegative, represented.presence, represented.size, represented.cursor⟩
  intro root member
  apply (represented.stored root member).frame
  · intros; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩




theorem Buckets.empty {state : Snapshot} (empty : ∀ degree, state.table degree < 0) :
    Buckets state [] := by
  refine ⟨by simp, by simp, ?_, by simp⟩
  intro degree occupied
  have negative := empty degree
  omega

theorem Buckets.perm {state : Snapshot} {before after : Forest} (buckets : Buckets state before)
    (permutation : after.Perm before) : Buckets state after := by
  refine ⟨(permutation.map Node.degree).nodup_iff.mpr buckets.unique, ?_, ?_, ?_⟩
  · intro root member
    exact buckets.read root (permutation.mem_iff.mp member)
  · intro degree occupied
    obtain ⟨root, member, same, read⟩ := buckets.complete degree occupied
    exact ⟨root, permutation.mem_iff.mpr member, same, read⟩
  · intro root member
    exact buckets.nonnegative root (permutation.mem_iff.mp member)

theorem Buckets.congr {before after : Snapshot} {roots : Forest} (buckets : Buckets before roots)
    (same : after.table = before.table) : Buckets after roots := by
  refine ⟨buckets.unique, ?_, ?_, buckets.nonnegative⟩
  · intro root member
    simpa only [same] using buckets.read root member
  · intro degree occupied
    simpa only [same] using buckets.complete degree (same ▸ occupied)

/-- Clearing the selected bucket removes exactly its root from scratch storage. -/
theorem Buckets.remove_head {state : Snapshot} {root : Node} {rest : Forest}
    (buckets : Buckets state (root :: rest)) :
    Buckets {state with table := Rings.write state.table root.degree (-1)} rest := by
  have separate := (List.nodup_cons.mp buckets.unique).1
  refine ⟨(List.nodup_cons.mp buckets.unique).2, ?_, ?_, ?_⟩
  · intro other member
    have different : (other.degree : Int) ≠ root.degree := by
      intro same
      have equal : other.degree = root.degree := by omega
      exact separate (List.mem_map.mpr ⟨other, member, equal⟩)
    simpa only [Rings.write, if_neg different] using buckets.read other (by simp [member])
  · intro degree occupied
    have different : degree ≠ root.degree := by
      intro same
      simp [Rings.write, same] at occupied
    change 0 ≤ Rings.write state.table root.degree (-1) degree at occupied
    rw [Rings.write, if_neg different] at occupied
    obtain ⟨other, member, readDegree, readVertex⟩ := buckets.complete degree occupied
    rcases List.mem_cons.mp member with rfl | tail
    · exact False.elim (different readDegree.symm)
    · exact ⟨other, tail, readDegree, by simpa only [Rings.write, if_neg different] using readVertex⟩
  · intro other member
    exact buckets.nonnegative other (by simp [member])









theorem Forest.marks_perm {before after : Forest} (permutation : after.Perm before) :
    after.marks = before.marks := by
  unfold Forest.marks
  exact (permutation.map Node.marks).sum_nat


theorem Forest.entries_perm {before after : Forest} (permutation : after.Perm before) :
    after.entries.Perm before.entries := by
  exact List.Perm.flatMap_right Node.entries permutation








































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci



theorem Snapshot.addRoot_fields (state : Snapshot) (vertex : Int)
    (root : state.parents vertex = -1) (unmarked : state.marks vertex = 0) (index : Int) :
    SameFields state (state.addRoot vertex) index := by
  constructor <;> simp [Snapshot.addRoot, Rings.write]
  · rintro rfl; exact root.symm
  · rintro rfl; exact unmarked.symm

theorem SplitRepresented.root_parent {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {vertex : Int}
    (member : vertex ∈ (pending ++ detached).map Node.vertex) : state.parents vertex = -1 := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  exact same ▸ (represented.stored root inForest).root_parent

theorem SplitRepresented.root_unmarked {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {node : Node}
    (member : node ∈ pending ++ detached) : state.marks node.vertex = 0 := by
  have unmarked := represented.valid.2.2.2 node member
  have stored := represented.stored node member
  cases stored with
  | node _ _ mark _ _ _ _ _ =>
    simp only [Node.marked] at unmarked
    simpa [Node.vertex, unmarked] using mark

/-- Only root pointers are changed, so every tree retains all its internal data. -/
theorem SplitRepresented.add_root_stored {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) {added : Node}
    (member : added ∈ detached) (root : Node) (inside : root ∈ pending ++ detached) :
    Stored (state.addRoot added.vertex) (-1) root := by
  have addedStored := represented.stored added (by simp [member])
  have unmarked := represented.root_unmarked (by simp [member] : added ∈ pending ++ detached)
  apply (represented.stored root inside).frame_roots
  · intro vertex key active
    exact represented.nonnegative vertex key (List.mem_flatMap.mpr ⟨root, inside, active⟩)
  · intro vertex key active
    exact state.addRoot_fields added.vertex addedStored.root_parent unmarked vertex
  · intro vertex _ nonroot
    have notAdded : vertex ≠ added.vertex := by
      intro same
      rw [same, addedStored.root_parent] at nonroot
      omega
    by_cases empty : state.minimum < 0
    · simp [Snapshot.addRoot, empty, Rings.write, notAdded]
    · obtain ⟨cursor, inPending, pointer⟩ := represented.cursor.resolve_left
        (by rintro ⟨_, minimum⟩; omega)
      have cursorMember : state.minimum ∈ pending.map Node.vertex := by
        rw [pointer]
        exact List.mem_map.mpr ⟨cursor, inPending, rfl⟩
      have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
        rcases represented.pendingRing with impossible | ring
        · simp [impossible] at cursorMember
        · exact ring
      have nextMember := (ring.neighbors cursorMember).2
      have parentCursor := represented.root_parent (by simp only [List.map_append, List.mem_append]; exact Or.inl cursorMember)
      have parentNext := represented.root_parent (by simp only [List.map_append, List.mem_append]; exact Or.inl nextMember)
      have notCursor : vertex ≠ state.minimum := by intro same; rw [same, parentCursor] at nonroot; omega
      have notNext : vertex ≠ state.right state.minimum := by intro same; rw [same, parentNext] at nonroot; omega
      simp [Snapshot.addRoot, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
        Rings.write, notAdded, notCursor, notNext]


/-- Existing detached singleton rings are disjoint from the new root-ring links. -/
theorem SplitRepresented.add_root_singletons {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (added : Node)
    (root : Node) (member : root ∈ detached) (different : root.vertex ≠ added.vertex) :
    (state.addRoot added.vertex).left root.vertex = root.vertex ∧
      (state.addRoot added.vertex).right root.vertex = root.vertex := by
  have original := represented.detachedRings root member
  by_cases empty : state.minimum < 0
  · simpa [Snapshot.addRoot, empty, Rings.write, different] using original
  · obtain ⟨cursor, inPending, pointer⟩ := represented.cursor.resolve_left
      (by rintro ⟨_, minimum⟩; omega)
    have cursorMember : state.minimum ∈ pending.map Node.vertex := by
      rw [pointer]
      exact List.mem_map.mpr ⟨cursor, inPending, rfl⟩
    have ring : Rings.Ring state.left state.right (pending.map Node.vertex) := by
      rcases represented.pendingRing with impossible | ring
      · simp [impossible] at cursorMember
      · exact ring
    have distinct (vertex : Int) (inside : vertex ∈ pending.map Node.vertex) : root.vertex ≠ vertex := by
      intro same
      apply represented.valid.1.roots_disjoint vertex inside
      apply List.mem_map.mpr
      exact ⟨(root.vertex, root.key), List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩, same⟩
    have notCursor := distinct _ cursorMember
    have notNext := distinct _ (ring.neighbors cursorMember).2
    simpa [Snapshot.addRoot, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
      Rings.write, different, notCursor, notNext] using original

/-- Rebuilding an empty pending ring moves one whole tree from detached roots. -/
theorem SplitRepresented.add_detached_empty {state : Snapshot} {added : Node} {rest : Forest}
    (represented : SplitRepresented state [] (added :: rest)) :
    SplitRepresented (state.addRoot added.vertex) [added] rest := by
  have minimum : state.minimum = -1 := by
    rcases represented.cursor with empty | ⟨root, impossible, _⟩
    · exact empty.2
    · simp at impossible
  refine ⟨represented.valid, ?_, ?_, ?_, represented.nonnegative,
    represented.presence, represented.size, ?_⟩
  · intro root member
    exact represented.add_root_stored (by simp) root member
  · apply Or.inr
    apply Rings.singleton_ring <;> simp [Snapshot.addRoot, minimum, Rings.write]
  · intro root member
    apply represented.add_root_singletons added root (by simp [member])
    intro same
    have separate := represented.valid.1.disjoint (front := [added]) (back := rest)
    apply separate added.vertex
    · exact ⟨added.key, List.mem_flatMap.mpr ⟨added, by simp, added.root_entry⟩⟩
    · exact ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
  · exact Or.inr ⟨added, by simp, by simp [Snapshot.addRoot, minimum]⟩

/-- With the cursor at the head, a detached tree is inserted immediately after
    it. The concatenated forest changes only by root permutation. -/
theorem SplitRepresented.add_detached_after_head {state : Snapshot} {head added : Node}
    {pending detached : Forest} (represented : SplitRepresented state (head :: pending) (added :: detached))
    (minimum : state.minimum = head.vertex) :
    SplitRepresented (state.addRoot added.vertex) (head :: added :: pending) detached := by
  have permutation : ((head :: added :: pending) ++ detached).Perm
      ((head :: pending) ++ added :: detached) := by
    simpa only [List.cons_append] using
      (List.perm_middle (a := added) (l₁ := pending) (l₂ := detached)).symm.cons head
  have contents := permutation.flatMap_right Node.entries
  have valid := represented.valid.perm permutation
  have nonnegative := represented.nonnegative head.vertex head.key
    (List.mem_flatMap.mpr ⟨head, by simp, head.root_entry⟩)
  have nonempty : ¬state.minimum < 0 := by omega
  have headNonnegative : ¬head.vertex < 0 := by omega
  have ring : Rings.Ring state.left state.right ((head :: pending).map Node.vertex) := by
    rcases represented.pendingRing with impossible | ring
    · simp at impossible
    · exact ring
  have fresh : added.vertex ∉ (head :: pending).map Node.vertex := by
    intro inside
    apply represented.valid.1.roots_disjoint added.vertex inside
    exact List.mem_map.mpr ⟨(added.vertex, added.key), List.mem_flatMap.mpr ⟨added, by simp, added.root_entry⟩, rfl⟩
  refine ⟨valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro root member
    exact represented.add_root_stored (by simp) root (permutation.mem_iff.mp member)
  · apply Or.inr
    simpa [Snapshot.addRoot, minimum, headNonnegative] using ring.insert_after fresh
  · intro root member
    apply represented.add_root_singletons added root (by simp [member])
    intro same
    have separate := valid.1.disjoint
    apply separate added.vertex
    · exact ⟨added.key, List.mem_flatMap.mpr ⟨added, by simp, added.root_entry⟩⟩
    · exact ⟨root.key, same ▸ List.mem_flatMap.mpr ⟨root, member, root.root_entry⟩⟩
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    exact (represented.presence vertex).trans
      ⟨fun ⟨key, member⟩ => ⟨key, contents.mem_iff.mpr member⟩,
        fun ⟨key, member⟩ => ⟨key, contents.mem_iff.mp member⟩⟩
  · change state.size = _
    rw [represented.size]
    exact congrArg Int.ofNat contents.length_eq.symm
  · by_cases better : state.keys added.vertex < state.keys state.minimum
    · exact Or.inr ⟨added, by simp, by simp [Snapshot.addRoot, nonempty, better]⟩
    · have notBetter : ¬state.keys added.vertex < state.keys head.vertex := by simpa only [minimum] using better
      exact Or.inr ⟨head, by simp, by simp [Snapshot.addRoot, minimum, headNonnegative, notBetter]⟩






end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- Move one detached tree into the pending root ring at its actual cursor. -/
theorem SplitRepresented.add_detached {state : Snapshot} {pending detached : Forest} {added : Node}
    (represented : SplitRepresented state pending (added :: detached)) :
    ∃ afterPending,
      SplitRepresented (state.addRoot added.vertex) afterPending detached ∧
      afterPending.Perm (added :: pending) := by
  cases pending with
  | nil => exact ⟨[added], represented.add_detached_empty, List.Perm.refl _⟩
  | cons head tail =>
    obtain ⟨cursor, member, pointer⟩ := represented.cursor.resolve_left (by simp)
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    have represented' : SplitRepresented state (front ++ cursor :: back) (added :: detached) := located ▸ represented
    have rotated := represented'.rotate_pending
    change SplitRepresented state (cursor :: (back ++ front)) (added :: detached) at rotated
    refine ⟨cursor :: added :: (back ++ front), rotated.add_detached_after_head pointer, ?_⟩
    have rotation : (cursor :: (back ++ front)).Perm (head :: tail) := by
      rw [located]
      simpa only [List.cons_append] using
        (List.perm_append_comm (l₁ := cursor :: back) (l₂ := front))
    exact (List.Perm.swap _ _ _).trans (rotation.cons added)



theorem SplitRepresented.pending_empty {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) : state.minimum < 0 ↔ pending = [] := by
  constructor
  · intro negative
    rcases represented.cursor with empty | ⟨root, member, pointer⟩
    · exact empty.1
    · have positive := represented.nonnegative root.vertex root.key
        (List.mem_flatMap.mpr ⟨root, by simp [member], root.root_entry⟩)
      omega
  · intro empty
    subst pending
    rcases represented.cursor with empty | ⟨root, impossible, _⟩
    · omega
    · simp at impossible

/-- Comparing the new root with the old cursor preserves the minimum invariant. -/
theorem SplitRepresented.add_detached_least {state : Snapshot} {pending detached afterPending : Forest}
    {added : Node} (represented : SplitRepresented state pending (added :: detached))
    (least : PendingLeast state pending) (permutation : afterPending.Perm (added :: pending)) :
    PendingLeast (state.addRoot added.vertex) afterPending := by
  have key := (represented.stored added (by simp)).root_key
  intro root member
  have member' := permutation.mem_iff.mp member
  simp only [List.mem_cons] at member'
  by_cases empty : state.minimum < 0
  · have noPending := represented.pending_empty.mp empty
    simp only [noPending, List.not_mem_nil, or_false] at member'
    subst root
    simp [Snapshot.addRoot, empty, key]
  · by_cases better : state.keys added.vertex < state.keys state.minimum
    · change state.keys (if state.minimum < 0 then added.vertex else
        if state.keys added.vertex < state.keys state.minimum then added.vertex else state.minimum) ≤ root.key
      rw [if_neg empty, if_pos better, key]
      rcases member' with rfl | member'
      · exact Int.le_refl _
      · have previous := least root member'
        omega
    · change state.keys (if state.minimum < 0 then added.vertex else
        if state.keys added.vertex < state.keys state.minimum then added.vertex else state.minimum) ≤ root.key
      rw [if_neg empty, if_neg better]
      rcases member' with rfl | member'
      · omega
      · exact least root member'






/-- One table scan either leaves the forest alone or moves exactly its selected
    detached tree into the pending root ring. -/
theorem SplitRepresented.rebuild_step {state : Snapshot} {pending detached : Forest}
    (represented : SplitRepresented state pending detached) (buckets : Buckets state detached)
    (least : PendingLeast state pending) (degree : Int) :
    ∃ afterPending afterDetached,
      SplitRepresented (state.rebuildAt degree) afterPending afterDetached ∧
      Buckets (state.rebuildAt degree) afterDetached ∧
      PendingLeast (state.rebuildAt degree) afterPending ∧
      (afterPending ++ afterDetached).Perm (pending ++ detached) ∧
      afterDetached.length + (if state.table degree < 0 then 0 else 1) = detached.length := by
  by_cases empty : state.table degree < 0
  · let cleared : Snapshot := {state with table := Rings.write state.table degree (-1)}
    have unchanged : Buckets cleared detached := by
      refine ⟨buckets.unique, ?_, ?_, buckets.nonnegative⟩
      · intro root member
        have read := buckets.read root member
        have positive := buckets.nonnegative root member
        have different : (root.degree : Int) ≠ degree := by intro same; rw [same] at read; omega
        simpa only [cleared, Rings.write, if_neg different] using read
      · intro index positive
        change 0 ≤ Rings.write state.table degree (-1) index at positive
        have different : index ≠ degree := by intro same; simp [Rings.write, same] at positive
        rw [Rings.write, if_neg different] at positive
        obtain ⟨root, member, same, read⟩ := buckets.complete index positive
        exact ⟨root, member, same, by simpa only [cleared, Rings.write, if_neg different] using read⟩
    refine ⟨pending, detached, ?_, ?_, ?_, List.Perm.refl _, by simp [empty]⟩
    · simpa only [Snapshot.rebuildAt, if_pos empty] using represented.table_write degree (-1)
    · simpa only [Snapshot.rebuildAt, if_pos empty] using unchanged
    · simpa only [Snapshot.rebuildAt, if_pos empty] using! least
  · have occupied : 0 ≤ state.table degree := by omega
    obtain ⟨root, member, readDegree, readVertex⟩ := buckets.complete degree occupied
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    let rest := back ++ front
    have rearranged : (root :: rest).Perm detached := by
      rw [located]
      simpa only [rest, List.cons_append] using
        (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
    have prepared := (represented.perm_detached rearranged).table_write degree (-1)
    have table := (buckets.perm rearranged).remove_head
    rw [readDegree] at table
    obtain ⟨afterPending, added, permutation⟩ := prepared.add_detached
    have afterLeast := prepared.add_detached_least least permutation
    have effect : state.rebuildAt degree =
        ({state with table := Rings.write state.table degree (-1)} : Snapshot).addRoot root.vertex := by
      simp only [Snapshot.rebuildAt, if_neg empty, readVertex]
    refine ⟨afterPending, rest, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [effect] using added
    · rw [effect]
      exact table.congr rfl
    · simpa only [effect] using afterLeast
    · have moved : (afterPending ++ rest).Perm (pending ++ root :: rest) := by
        apply (permutation.append_right rest).trans
        simpa only [List.cons_append] using
          (List.perm_middle (a := root) (l₁ := pending) (l₂ := rest)).symm
      exact moved.trans (rearranged.append_left pending)
    · have length := rearranged.length_eq
      simp only [List.length_cons] at length
      simp only [if_neg empty]
      omega






theorem Buckets.cleared_negative {state : Snapshot} {roots : Forest} (buckets : Buckets state roots) :
    ClearedBelow state 0 := by
  intro index negative
  by_cases negativeValue : state.table index < 0
  · exact negativeValue
  have nonnegative : 0 ≤ state.table index := by omega
  obtain ⟨root, _, degree, _⟩ := buckets.complete index nonnegative
  omega

theorem rebuild_scratch_bound (state : Snapshot) (degree maximum : Int) (bound : ScratchBound state maximum) :
    ScratchBound (state.rebuildAt degree) maximum := by
  intro index above
  rw [Snapshot.rebuildAt_table]
  unfold Rings.write
  split
  · omega
  · exact bound index above

theorem rebuild_cleared (state : Snapshot) (degree : Int) (cleared : ClearedBelow state degree) :
    ClearedBelow (state.rebuildAt degree) (degree + 1) := by
  intro index below
  rw [Snapshot.rebuildAt_table]
  unfold Rings.write
  split
  · omega
  · exact cleared index (by omega)

theorem SplitRepresented.finish {state : Snapshot} {pending : Forest}
    (represented : SplitRepresented state pending []) (least : PendingLeast state pending)
    (scratch : ∀ degree, state.table degree < 0) : Represented state pending := by
  refine ⟨by simpa using represented.valid, represented.pendingRing, ?_, ?_, ?_, ?_, ?_, scratch⟩
  · intro root member
    exact represented.stored root (by simpa using member)
  · simpa using represented.nonnegative
  · simpa [Forest.Has] using represented.presence
  · simpa using represented.size
  · rcases represented.cursor with empty | ⟨root, member, pointer⟩
    · exact Or.inl empty
    · refine Or.inr ⟨root, member, pointer, ?_⟩
      have key := (represented.stored root (by simpa using member)).root_key
      intro other inside
      have bound := least other inside
      rw [pointer, key] at bound
      exact bound

/-- The entire table reconstruction terminates over a finite interval. It
    preserves every entry, clears scratch storage, and makes at most one key
    comparison per moved root. -/
theorem rebuild_interval (state : Snapshot) (pending detached : Forest) (degree maximum : Int)
    (represented : SplitRepresented state pending detached) (buckets : Buckets state detached)
    (least : PendingLeast state pending) (bound : ScratchBound state maximum)
    (cleared : ClearedBelow state degree) :
    ∃ after finalPending insertions comparisons,
      BucketRebuild maximum state degree after insertions comparisons ∧
      Represented after finalPending ∧ finalPending.Perm (pending ++ detached) ∧
      insertions = detached.length ∧ comparisons ≤ insertions := by
  have terminate : ∀ fuel : Nat, ∀ before pending detached index,
      (maximum + 1 - index).toNat = fuel → SplitRepresented before pending detached →
      Buckets before detached → PendingLeast before pending → ScratchBound before maximum →
      ClearedBelow before index →
      ∃ after finalPending insertions comparisons,
        BucketRebuild maximum before index after insertions comparisons ∧
        Represented after finalPending ∧ finalPending.Perm (pending ++ detached) ∧
        insertions = detached.length ∧ comparisons ≤ insertions := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro before pending detached index measure valid table minimum bounded cleared
      by_cases done : maximum < index
      · have scratch : ∀ i, before.table i < 0 := by
          intro i
          by_cases below : i < index
          · exact cleared i below
          · exact bounded i (by omega)
        have noDetached : detached = [] := by
          cases detached with
          | nil => rfl
          | cons root tail =>
            have read := table.read root (by simp)
            have positive := table.nonnegative root (by simp)
            have negative := scratch root.degree
            omega
        subst detached
        exact ⟨before, pending, 0, 0, .done _ _ done, valid.finish minimum scratch,
          by simp, rfl, Nat.zero_le _⟩
      have inside : index ≤ maximum := by omega
      have smaller : (maximum + 1 - (index + 1)).toNat < fuel := by omega
      obtain ⟨nextPending, nextDetached, nextValid, nextTable, nextLeast, permutation, count⟩ :=
        valid.rebuild_step table minimum index
      obtain ⟨after, finalPending, insertions, comparisons, rest, finalValid, contents, moved, charged⟩ :=
        ih _ smaller (before.rebuildAt index) nextPending nextDetached (index + 1) rfl
          nextValid nextTable nextLeast (rebuild_scratch_bound _ _ _ bounded)
          (rebuild_cleared _ _ cleared)
      by_cases empty : before.table index < 0
      · refine ⟨after, finalPending, insertions, comparisons, .skip inside empty rest,
          finalValid, contents.trans permutation, ?_, charged⟩
        simp only [if_pos empty, Nat.add_zero] at count
        omega
      · refine ⟨after, finalPending, insertions + 1,
          comparisons + (if before.minimum < 0 then 0 else 1), .insert inside (by omega) rest,
          finalValid, contents.trans permutation, ?_, ?_⟩
        · simp only [if_neg empty] at count
          omega
        · split <;> omega
  exact terminate _ state pending detached degree rfl represented buckets least bound cleared

/-- Starting from the consolidated buckets produces a complete represented
    heap with distinct root degrees and the same roots, hence the same entries. -/
theorem rebuild_complete (state : Snapshot) (detached : Forest) (maximum : Int)
    (represented : SplitRepresented state [] detached) (buckets : Buckets state detached)
    (bound : ScratchBound state maximum) :
    ∃ after forest comparisons,
      BucketRebuild maximum state 0 after detached.length comparisons ∧
      Represented after forest ∧ forest.Perm detached ∧
      (forest.map Node.degree).Nodup ∧ comparisons ≤ forest.length := by
  obtain ⟨after, forest, insertions, comparisons, execution, ready, contents, count, charged⟩ :=
    rebuild_interval state [] detached 0 maximum represented buckets (by simp [PendingLeast])
      bound buckets.cleared_negative
  simp only [List.nil_append] at contents
  subst insertions
  exact ⟨after, forest, comparisons, execution, ready, contents,
    (contents.map Node.degree).nodup_iff.mpr buckets.unique, contents.length_eq ▸ charged⟩


/-- Occupied buckets lie within the recorded maximum degree. -/
theorem Buckets.within_scratch_bound {state : Snapshot} {roots : Forest} {maximum : Int}
    (buckets : Buckets state roots) (bound : ScratchBound state maximum)
    (root : Node) (member : root ∈ roots) : root.degree ≤ maximum.toNat := by
  have read := buckets.read root member
  have positive := buckets.nonnegative root member
  have degree : (root.degree : Int) ≤ maximum := by
    by_cases above : maximum < root.degree
    · have negative := bound root.degree above
      omega
    · omega
  omega

/-- Distinct degrees bound the number of roots reconnected during rebuild. -/
theorem Buckets.roots_bound {state : Snapshot} {roots : Forest} {maximum : Int}
    (buckets : Buckets state roots) (bound : ScratchBound state maximum) :
    roots.length ≤ maximum.toNat + 1 := by
  have count := distinct_degrees_bound (roots.map Node.degree) maximum.toNat buckets.unique
    (by
      intro degree member
      obtain ⟨root, inside, same⟩ := List.mem_map.mp member
      rw [← same]
      exact buckets.within_scratch_bound bound root inside)
  simpa only [List.length_map] using count

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


theorem remove_from_ring_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    FibonacciHeap.remove_from_ring.Call heap (queue, vertex)
      (removeHeap heap layout vertex) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc8 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc7 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc6 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc5 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc4 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc3 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc2 _ _ _)
  simp only [left_write, right_write, valid.readLeft, valid.readRight,
    Option.getD_some, removeHeap]
  exact Reaches.single (Step.FibonacciHeap_remove_from_ring_pc1 _ _ _)

theorem remove_preserves_layout (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    layout.Valid (removeHeap heap layout vertex) queue := by
  exact ⟨valid.object, valid.readKeys, valid.readParents, valid.readChildren, valid.readLeft, valid.readRight, valid.readDegrees, valid.readMarks, valid.readPresent, valid.readTable, valid.readMinimum, valid.readSize, valid.keysAllocated, valid.parentsAllocated, valid.childrenAllocated, valid.leftAllocated, valid.rightAllocated, valid.degreesAllocated, valid.marksAllocated, valid.presentAllocated, valid.tableAllocated, valid.separate⟩







-- Initialization follows the source allocation order. The exact-effect
-- statement can be reused without opening this method's transition rules.
















































































-- A link's compiled contract is independent of any whole-heap invariant.
-- Its callers separately establish equal degree, key order, and disjoint trees.


theorem link_preserves_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (child parent : Int) :
    layout.Valid (linkHeap heap layout child parent) queue := by
  unfold linkHeap
  apply Layout.Valid.tick
  apply Layout.Valid.write
  apply Layout.Valid.write
  unfold linkRingHeap
  dsimp only
  split
  · repeat apply Layout.Valid.write
    exact valid
  · repeat apply Layout.Valid.write
    exact valid












-- The proof composes the checked ring-removal and root-insertion contracts.
-- Their internal transitions are not revisited when a cut is verified.


theorem Layout.Valid.set_minimum (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (minimum : Int) :
    { layout with minimum := minimum }.Valid (set_FibonacciHeap_minimum heap queue minimum) queue := by
  constructor
  · simpa [set_FibonacciHeap_minimum, is_FibonacciHeap] using valid.object
  · simpa [field_FibonacciHeap_keys, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readKeys
  · simpa [field_FibonacciHeap_parents, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readParents
  · simpa [field_FibonacciHeap_children, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readChildren
  · simpa [field_FibonacciHeap_left, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readLeft
  · simpa [field_FibonacciHeap_right, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readRight
  · simpa [field_FibonacciHeap_degrees, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readDegrees
  · simpa [field_FibonacciHeap_marks, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readMarks
  · simpa [field_FibonacciHeap_present, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readPresent
  · simpa [field_FibonacciHeap_table, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readTable
  · exact field_FibonacciHeap_minimum_set heap queue minimum valid.object
  · simpa [field_FibonacciHeap_size, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readSize
  · exact valid.keysAllocated
  · exact valid.parentsAllocated
  · exact valid.childrenAllocated
  · exact valid.leftAllocated
  · exact valid.rightAllocated
  · exact valid.degreesAllocated
  · exact valid.marksAllocated
  · exact valid.presentAllocated
  · exact valid.tableAllocated
  · exact valid.separate



theorem add_root_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (addRootLayout heap layout vertex).Valid (addRootHeap heap queue layout vertex) queue := by
  unfold addRootHeap addRootLayout
  dsimp only
  split
  · apply Layout.Valid.set_minimum
    repeat apply Layout.Valid.write
    exact valid
  · split
    · apply Layout.Valid.set_minimum
      apply Layout.Valid.tick
      repeat apply Layout.Valid.write
      exact valid
    · apply Layout.Valid.tick
      repeat apply Layout.Valid.write
      exact valid





















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







theorem rebuild_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree : Int) :
    (rebuildLayout heap layout degree).Valid (rebuildHeap heap queue layout degree) queue := by
  unfold rebuildLayout rebuildHeap
  dsimp only
  split
  · exact Layout.Valid.write _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _ _
  · exact add_root_layout _ _ _ (Layout.Valid.write _ _ _
      (Layout.Valid.tick _ _ _ valid _ _) _ _ _) _





private theorem rebuild_effect_reaches (queue : Ref_FibonacciHeap) (maximum : Int)
    (heap after : Heap) (layout finalLayout : Layout) (degree : Int)
    (valid : layout.Valid heap queue)
    (effect : RebuildEffect queue maximum heap layout degree after finalLayout)
    (state : State_FibonacciHeap_consolidate) (stack : Stack) :
    Reaches Step (.active heap (.fn_FibonacciHeap_consolidate 4
      { state with v0 := queue, v1 := layout.table, v2 := maximum, v4 := degree }) stack)
      (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
  induction effect generalizing state with
  | done heap layout degree finished =>
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc4 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc3_false _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc2 _ _ _)
    exact Reaches.single (Step.FibonacciHeap_consolidate_pc1 _ _ _)
  | @step heap after layout finalLayout degree remaining rest ih =>
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc4 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc3_true _ _ _ (by simp [remaining]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc14 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc13 _ _ _ valid.tableAllocated)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc12 _ _ _ valid.tableAllocated)
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc11 _ _ _)
    have nextValid := rebuild_layout heap queue layout valid degree
    by_cases absent : heap.read layout.table degree < 0
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc10_false _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc5 _ _ _)
      simpa only [rebuildHeap, rebuildLayout, absent, ↓reduceIte, rebuildClear, Heap.read_tick] using
        ih nextValid { state with t8 := decide (degree ≤ maximum), t9 := decide (heap.read layout.table degree ≥ 0), v3 := heap.read layout.table degree }
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc10_true _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc9 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc8 _ _ _ valid.object)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc7 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc6 _ _ _)
      have clearValid : layout.Valid (rebuildClear heap layout degree) queue :=
        Layout.Valid.write _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _ _
      apply Reaches.trans ((add_root_summary _ _ _ clearValid (heap.read layout.table degree)).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc5 _ _ _)
      have tableSame : (rebuildLayout heap layout degree).table = layout.table := by
        simp only [rebuildLayout, absent, ↓reduceIte]
        unfold addRootLayout
        split
        · rfl
        · dsimp only
          split <;> rfl
      have subsequent := ih nextValid { state with t8 := decide (degree ≤ maximum), t9 := decide (heap.read layout.table degree ≥ 0), v3 := heap.read layout.table degree, t10 := (), t11 := queue, t12 := heap.read layout.table degree }
      rw [tableSame] at subsequent
      simpa only [rebuildHeap, absent, ↓reduceIte, Heap.read_tick] using subsequent









theorem collision_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree : Int) :
    layout.Valid (collisionHeap heap layout vertex degree) queue := by
  apply link_preserves_layout
  apply Layout.Valid.tick
  exact Layout.Valid.write _ _ _ valid _ _ _











private theorem collision_effect_reaches (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (vertex degree finalVertex finalDegree : Int) (links : Nat)
    (valid : layout.Valid heap queue)
    (effect : CollisionEffect layout heap vertex degree after finalVertex finalDegree links)
    (state : State_FibonacciHeap_consolidate) (stack : Stack) :
    ∃ finalState : State_FibonacciHeap_consolidate,
      finalState.v0 = queue ∧ finalState.v1 = layout.table ∧ finalState.v2 = state.v2 ∧
      finalState.v3 = finalVertex ∧ finalState.v4 = finalDegree ∧
      Reaches Step (.active heap (.fn_FibonacciHeap_consolidate 23
        {state with v0 := queue, v1 := layout.table, v3 := vertex, v4 := degree}) stack)
        (.active after (.fn_FibonacciHeap_consolidate 21 finalState) stack) := by
  induction effect generalizing state with
  | done heap vertex degree empty =>
    refine ⟨{state with v0 := queue, v1 := layout.table, v3 := vertex, v4 := degree, t15 := decide (heap.read layout.table degree ≥ 0)}, rfl, rfl, rfl, rfl, rfl, ?_⟩
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc23 _ _ _ valid.tableAllocated)
    exact Reaches.single (Step.FibonacciHeap_consolidate_pc22_false _ _ _ (by simp; omega))
  | @step heap after vertex degree finalVertex finalDegree links occupied rest ih =>
    let ready := collisionStart heap layout degree
    let other := heap.read layout.table degree
    have readyValid : layout.Valid ready queue :=
      Layout.Valid.tick _ _ _ (Layout.Valid.write _ _ _ valid _ _ _) _ _
    have nextValid := collision_layout heap queue layout valid vertex degree
    by_cases better : ready.read layout.keys other < ready.read layout.keys vertex
    · dsimp only [ready, other, collisionStart] at better
      let nextState : State_FibonacciHeap_consolidate :=
        {state with v0 := queue, v1 := layout.table, v3 := other, v4 := degree + 1, v5 := vertex, v6 := vertex, t15 := decide (heap.read layout.table degree ≥ 0), t16 := (), t17 := queue, t18 := vertex, t19 := other, t20 := decide (ready.read layout.keys other < ready.read layout.keys vertex)}
      obtain ⟨finalState, self, table, maximum, output, degreeOut, tail⟩ := ih nextValid nextState
      refine ⟨finalState, self, table, maximum, output, degreeOut, ?_⟩
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc23 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc22_true _ _ _ (by simp [occupied]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc37 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc36 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc35 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc34 _ _ _
        (by simp [valid.readKeys, valid.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc33_true _ _ _
        (by simpa only [keys_tick, keys_write, valid.readKeys, Option.getD_some, decide_eq_true_eq, decide_eq_false_iff_not] using better))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc32 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc31 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc30 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc29 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc28 _ _ _ readyValid.object)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc27 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc26 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc25 _ _ _)
      apply Reaches.trans ((link_summary ready queue layout readyValid vertex other).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc24 _ _ _)
      simpa only [collisionHeap, collisionParent, collisionChild, collisionStart, better, ↓reduceIte,
        nextState, ready, other, keys_tick, keys_write, valid.readKeys, Option.getD_some] using tail
    · dsimp only [ready, other, collisionStart] at better
      let nextState : State_FibonacciHeap_consolidate :=
        {state with v0 := queue, v1 := layout.table, v3 := vertex, v4 := degree + 1, v5 := other, t15 := decide (heap.read layout.table degree ≥ 0), t16 := (), t17 := queue, t18 := other, t19 := vertex, t20 := decide (ready.read layout.keys other < ready.read layout.keys vertex)}
      obtain ⟨finalState, self, table, maximum, output, degreeOut, tail⟩ := ih nextValid nextState
      refine ⟨finalState, self, table, maximum, output, degreeOut, ?_⟩
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc23 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc22_true _ _ _ (by simp [occupied]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc37 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc36 _ _ _ valid.tableAllocated)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc35 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc34 _ _ _
        (by simp [valid.readKeys, valid.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc33_false _ _ _
        (by simpa only [keys_tick, keys_write, valid.readKeys, Option.getD_some, decide_eq_true_eq, decide_eq_false_iff_not] using better))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc29 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc28 _ _ _ readyValid.object)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc27 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc26 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc25 _ _ _)
      apply Reaches.trans ((link_summary ready queue layout readyValid other vertex).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc24 _ _ _)
      simpa only [collisionHeap, collisionParent, collisionChild, collisionStart, better, ↓reduceIte,
        nextState, ready, other, keys_tick, keys_write, valid.readKeys, Option.getD_some] using tail







theorem detach_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) : (detachLayout heap layout).Valid (detachHeap heap queue layout) queue := by
  apply Layout.Valid.tick
  apply remove_preserves_layout
  exact Layout.Valid.set_minimum heap queue layout valid (pendingMinimum heap layout)

theorem CollisionEffect.layout_valid {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout : Layout} {vertex degree finalVertex finalDegree : Int} {links : Nat}
    (effect : CollisionEffect layout heap vertex degree after finalVertex finalDegree links)
    (valid : layout.Valid heap queue) : layout.Valid after queue := by
  induction effect with
  | done => exact valid
  | step occupied rest ih => exact ih (collision_layout _ _ _ valid _ _)



private theorem consume_effect_reaches (queue : Ref_FibonacciHeap)
    (heap after : Heap) (layout finalLayout : Layout) (maximum : Int) (roots links : Nat)
    (valid : layout.Valid heap queue)
    (effect : ConsumeEffect queue heap layout maximum after finalLayout roots links)
    (state : State_FibonacciHeap_consolidate) (stack : Stack) :
    Reaches Step (.active heap (.fn_FibonacciHeap_consolidate 17
      {state with v0 := queue, v1 := layout.table, v2 := maximum}) stack)
      (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
  induction effect generalizing state with
  | @done heap after layout finalLayout maximum empty rebuild =>
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc17 _ _ _ (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc16_false _ _ _ (by simp [valid.readMinimum]; omega))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc15 _ _ _)
    simpa only [valid.readMinimum, Option.getD_some] using
      rebuild_effect_reaches queue maximum heap after layout finalLayout 0 valid rebuild
        {state with t13 := decide (layout.minimum ≥ 0)} stack
  | @next heap merged after layout finalLayout maximum vertex degree links tailRoots tailLinks pending collisions rest ih =>
    let detached := detachHeap heap queue layout
    let detachedLayout := detachLayout heap layout
    have detachedReady := detach_layout heap queue layout valid
    have mergedReady := collisions.layout_valid detachedReady
    have storedReady := Layout.Valid.write merged queue detachedLayout mergedReady layout.table degree vertex
    have finish (atCollision : State_FibonacciHeap_consolidate)
        (readSelf : atCollision.v0 = queue) (readTable : atCollision.v1 = layout.table)
        (readMaximum : atCollision.v2 = maximum) (readVertex : atCollision.v3 = layout.minimum)
        (readDegree : atCollision.v4 = detached.read layout.degrees layout.minimum) :
        Reaches Step (.active detached (.fn_FibonacciHeap_consolidate 23 atCollision) stack)
          (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
      obtain ⟨last, self, table, maximumSame, vertexSame, degreeSame, collisionRun⟩ :=
        collision_effect_reaches detached merged queue detachedLayout layout.minimum
          (detached.read layout.degrees layout.minimum) vertex degree links detachedReady collisions atCollision stack
      have actual : {atCollision with v0 := queue, v1 := detachedLayout.table, v3 := layout.minimum, v4 := detached.read layout.degrees layout.minimum} = atCollision := by
        cases atCollision
        simp_all [detachedLayout, detachLayout]
      rw [actual] at collisionRun
      apply Reaches.trans collisionRun
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc21 _ _ _ (by simpa [table] using mergedReady.tableAllocated))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc20 _ _ _)
      have maximumValue : last.v2 = maximum := maximumSame.trans readMaximum
      by_cases larger : maximum < degree
      · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc19_true _ _ _ (by simp [degreeSame, maximumValue, larger]))
        apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc18 _ _ _)
        have next := ih storedReady {last with t14 := decide (degree > maximum)}
        simpa only [self, table, degreeSame, vertexSame, maximumValue, Int.max_eq_right (Int.le_of_lt larger), detachedLayout, detachLayout] using next
      · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc19_false _ _ _ (by simp [degreeSame, maximumValue, larger]))
        have next := ih storedReady {last with t14 := decide (degree > maximum)}
        simpa only [self, table, degreeSame, vertexSame, maximumValue, Int.max_eq_left (by omega : degree ≤ maximum), detachedLayout, detachLayout] using next
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc17 _ _ _ (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc16_true _ _ _ (by simp [valid.readMinimum, pending]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc48 _ _ _ (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc47 _ _ _ (by simp [valid.readRight, valid.rightAllocated]))
    have tail (prepared : Heap) (current : Layout) (ready : current.Valid prepared queue)
        (sameRefs : current.keys = layout.keys ∧ current.parents = layout.parents ∧ current.children = layout.children ∧
          current.left = layout.left ∧ current.right = layout.right ∧ current.degrees = layout.degrees ∧
          current.marks = layout.marks ∧ current.present = layout.present ∧ current.table = layout.table)
        (state : State_FibonacciHeap_consolidate) (self : state.v0 = queue) (table : state.v1 = layout.table)
        (maximumValue : state.v2 = maximum) (vertexValue : state.v3 = layout.minimum)
        (sameHeap : (removeHeap prepared current layout.minimum).tick "heap_root_scans" = detached) :
        Reaches Step (.active prepared (.fn_FibonacciHeap_consolidate 43 state) stack)
          (resumeConfig after (.fn_FibonacciHeap_consolidate ()) stack) := by
      have detachedReady' := Layout.Valid.tick (removeHeap prepared current layout.minimum) queue current (remove_preserves_layout prepared queue current ready layout.minimum) "heap_root_scans" 1
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc43 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc42 _ _ _ (by simpa [self] using ready.object))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc41 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc40 _ _ _)
      simp only [self, vertexValue]
      apply Reaches.trans ((remove_from_ring_summary prepared queue current ready layout.minimum).2 _)
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc39 _ _ _)
      rw [sameHeap]
      have readyDetached : current.Valid detached queue := sameHeap ▸ detachedReady'
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc38 _ _ _
        (by rw [readyDetached.readDegrees]; exact ⟨rfl, readyDetached.degreesAllocated⟩))
      simp only [readyDetached.readDegrees, Option.getD_some, sameRefs.2.2.2.2.2.1]
      exact finish _ rfl table maximumValue rfl rfl
    by_cases singleton : heap.read layout.right layout.minimum = layout.minimum
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc46_true _ _ _ (by simp [valid.readMinimum, valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc44 _ _ _ valid.object)
      apply tail _ {layout with minimum := -1} (Layout.Valid.set_minimum heap queue layout valid (-1))
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ rfl rfl rfl
        (by simp [valid.readMinimum])
      simp [detached, detachHeap, pendingMinimum, singleton, removeHeap]
    · apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc46_false _ _ _ (by simp [valid.readMinimum, valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc45 _ _ _ (by simp [valid.readRight, valid.rightAllocated, valid.object]))
      simp only [valid.readMinimum, valid.readRight, Option.getD_some]
      apply tail _ {layout with minimum := heap.read layout.right layout.minimum}
        (Layout.Valid.set_minimum heap queue layout valid _) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ rfl rfl rfl rfl
      simp [detached, detachHeap, pendingMinimum, singleton, removeHeap]

/-- All three consolidation phases compose through checked local call summaries. -/
theorem consolidate_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (roots links : Nat) (valid : layout.Valid heap queue)
    (effect : ConsumeEffect queue heap layout (-1) after finalLayout roots links) :
    FibonacciHeap.consolidate.Call heap queue after () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc50 _ _ _ (by simp [valid.readTable]))
  apply Reaches.prepend (Step.FibonacciHeap_consolidate_pc49 _ _ _)
  simpa only [valid.readTable, Option.getD_some] using
    consume_effect_reaches queue heap after layout finalLayout (-1) roots links valid effect {} stack


private theorem snapshot_ext (before after : Algo2Lean.Fibonacci.Snapshot)
    (keys : before.keys = after.keys) (parents : before.parents = after.parents)
    (children : before.children = after.children) (left : before.left = after.left)
    (right : before.right = after.right) (degrees : before.degrees = after.degrees)
    (marks : before.marks = after.marks) (present : before.present = after.present)
    (table : before.table = after.table) (minimum : before.minimum = after.minimum)
    (size : before.size = after.size) : before = after := by
  cases before
  cases after
  simp_all









































/-- Root insertion matches the forest-storage effect for any detached tree. -/
theorem add_root_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    snapshot (addRootHeap heap queue layout vertex) (addRootLayout heap layout vertex) =
      (snapshot heap layout).addRoot vertex := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  by_cases empty : layout.minimum < 0
  · apply snapshot_ext
    all_goals try funext index
    all_goals simp [snapshot, addRootHeap, addRootLayout, rootHeaderHeap, set_FibonacciHeap_minimum, Heap.read,
      Heap.write, Heap.writeField, Algo2Lean.Fibonacci.Snapshot.addRoot,
      Algo2Lean.Fibonacci.Rings.write, empty, keys_parents, keys_left, keys_right, keys_marks,
      parents_left, parents_right, parents_marks, children_left, children_right, children_marks,
      left_right, left_marks, right_marks, degrees_marks, Ne.symm parents_children, Ne.symm
      parents_left, Ne.symm parents_right, Ne.symm parents_degrees, Ne.symm parents_marks, Ne.symm
      parents_present, Ne.symm parents_table, Ne.symm left_right, Ne.symm left_degrees, Ne.symm
      left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm right_degrees, Ne.symm
      right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm marks_present, Ne.symm
      marks_table]
  · by_cases smaller : heap.read layout.keys vertex < heap.read layout.keys layout.minimum
    all_goals
      simp only [Heap.read] at smaller
      apply snapshot_ext
      all_goals try funext index
      all_goals simp [snapshot, addRootHeap, addRootLayout, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
      Heap.read, Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Snapshot.addRoot,
      Algo2Lean.Fibonacci.Rings.write, Algo2Lean.Fibonacci.Rings.insertAfterLeft,
      Algo2Lean.Fibonacci.Rings.insertAfterRight, empty, smaller, keys_parents, keys_left,
      keys_right, keys_marks, parents_left, parents_right, parents_marks, children_left,
      children_right, children_marks, left_right, left_marks, right_marks, degrees_marks, Ne.symm
      parents_children, Ne.symm parents_left, Ne.symm parents_right, Ne.symm parents_degrees,
      Ne.symm parents_marks, Ne.symm parents_present, Ne.symm parents_table, Ne.symm left_right,
      Ne.symm left_degrees, Ne.symm left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm
      right_degrees, Ne.symm right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm
      marks_present, Ne.symm marks_table]




theorem table_write_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree value : Int) :
    snapshot (heap.write layout.table degree value) layout =
      {snapshot heap layout with table := Algo2Lean.Fibonacci.Rings.write (heap.read layout.table) degree value} := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, Heap.read, Heap.write,
    Algo2Lean.Fibonacci.Rings.write, keys, parents, children, left, right, degrees, marks, present]

private theorem rebuild_clear_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree : Int) :
    snapshot (rebuildClear heap layout degree) layout =
      {snapshot heap layout with table := Algo2Lean.Fibonacci.Rings.write (heap.read layout.table) degree (-1)} := by
  exact table_write_snapshot (heap.tick "heap_degree_scans") queue layout
    (Layout.Valid.tick _ _ _ valid _ _) degree (-1)

/-- A compiler-level table visit implements exactly the pure reconstruction step. -/
theorem rebuild_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree : Int) :
    snapshot (rebuildHeap heap queue layout degree) (rebuildLayout heap layout degree) =
      (snapshot heap layout).rebuildAt degree := by
  unfold rebuildHeap rebuildLayout Algo2Lean.Fibonacci.Snapshot.rebuildAt
  dsimp only
  have readTable : (snapshot heap layout).table = heap.read layout.table := rfl
  simp only [readTable]
  by_cases empty : heap.read layout.table degree < 0
  · simp only [if_pos empty]
    exact rebuild_clear_snapshot heap queue layout valid degree
  · simp only [if_neg empty]
    have ready : layout.Valid (rebuildClear heap layout degree) queue :=
      Layout.Valid.write _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _ _
    rw [add_root_snapshot _ _ _ ready]
    rw [rebuild_clear_snapshot heap queue layout valid degree]

theorem rebuild_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (degree : Int) (clock : String) :
    (rebuildHeap heap queue layout degree).clocks clock = heap.clocks clock +
      Clocks.single "heap_degree_scans" 1 clock + Clocks.single "heap_comparisons"
        (if heap.read layout.table degree < 0 then 0 else if layout.minimum < 0 then 0 else 1) clock := by
  unfold rebuildHeap
  dsimp only
  split
  · by_cases scan : clock = "heap_degree_scans" <;> simp_all [rebuildClear, Clocks.single]
  · rw [add_root_clocks]
    by_cases scan : clock = "heap_degree_scans" <;> simp_all [rebuildClear, Clocks.single]

/-- Every finite pure reconstruction is realized by the compiled loop, with
    exactly its comparisons and one degree-scan tick per visited bucket. -/
theorem realize_bucket_rebuild (maximum : Int) (before after : Algo2Lean.Fibonacci.Snapshot)
    (degree : Int) (insertions comparisons : Nat)
    (execution : Algo2Lean.Fibonacci.BucketRebuild maximum before degree after insertions comparisons)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ finalHeap finalLayout,
      RebuildEffect queue maximum heap layout degree finalHeap finalLayout ∧
      finalLayout.Valid finalHeap queue ∧ snapshot finalHeap finalLayout = after ∧
      ∀ clock, finalHeap.clocks clock = heap.clocks clock +
        Clocks.single "heap_degree_scans" (maximum + 1 - degree).toNat clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  induction execution generalizing heap layout with
  | done state degree past =>
    refine ⟨heap, layout, .done _ _ _ past, valid, observed, ?_⟩
    intro clock
    have zero : (maximum + 1 - degree).toNat = 0 := by omega
    simp [zero, Clocks.single]
  | @skip state final index count comparisons inside empty rest ih =>
    have next : snapshot (rebuildHeap heap queue layout index) (rebuildLayout heap layout index) =
        state.rebuildAt index := by rw [rebuild_snapshot heap queue layout valid, observed]
    obtain ⟨finalHeap, finalLayout, effect, ready, result, clocks⟩ :=
      ih (rebuildHeap heap queue layout index) (rebuildLayout heap layout index)
        (rebuild_layout heap queue layout valid index) next
    refine ⟨finalHeap, finalLayout, .step inside effect, ready, result, ?_⟩
    have empty' : heap.read layout.table index < 0 := by
      change (snapshot heap layout).table index < 0
      rw [observed]
      exact empty
    have count : (maximum + 1 - index).toNat = (maximum + 1 - (index + 1)).toNat + 1 := by omega
    intro clock
    rw [clocks, rebuild_clocks]
    simp only [if_pos empty']
    by_cases scan : clock = "heap_degree_scans" <;> by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [Clocks.single] <;> omega
  | @insert state final index count comparisons inside occupied rest ih =>
    have next : snapshot (rebuildHeap heap queue layout index) (rebuildLayout heap layout index) =
        state.rebuildAt index := by rw [rebuild_snapshot heap queue layout valid, observed]
    obtain ⟨finalHeap, finalLayout, effect, ready, result, clocks⟩ :=
      ih (rebuildHeap heap queue layout index) (rebuildLayout heap layout index)
        (rebuild_layout heap queue layout valid index) next
    refine ⟨finalHeap, finalLayout, .step inside effect, ready, result, ?_⟩
    have occupied' : ¬heap.read layout.table index < 0 := by
      have same : heap.read layout.table index = state.table index := congrArg (fun s => s.table index) observed
      omega
    have minimum : layout.minimum = state.minimum := congrArg Algo2Lean.Fibonacci.Snapshot.minimum observed
    have count : (maximum + 1 - index).toNat = (maximum + 1 - (index + 1)).toNat + 1 := by omega
    intro clock
    rw [clocks, rebuild_clocks]
    simp only [if_neg occupied', minimum]
    by_cases scan : clock = "heap_degree_scans" <;> by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [Clocks.single] <;> omega

/-- Reconstruction of finite degree buckets produces a complete heap and the
    exact compiled scan/comparison costs; clients need no loop transcript. -/
theorem rebuild_from_buckets (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (roots : Algo2Lean.Fibonacci.Forest) (maximum : Int)
    (represented : Algo2Lean.Fibonacci.SplitRepresented (snapshot heap layout) [] roots)
    (buckets : Algo2Lean.Fibonacci.Buckets (snapshot heap layout) roots)
    (bound : Algo2Lean.Fibonacci.ScratchBound (snapshot heap layout) maximum) :
    ∃ finalHeap finalLayout forest comparisons,
      RebuildEffect queue maximum heap layout 0 finalHeap finalLayout ∧
      QueueRep finalHeap queue finalLayout forest ∧ forest.Perm roots ∧
      (forest.map Algo2Lean.Fibonacci.Node.degree).Nodup ∧ comparisons ≤ forest.length ∧
      Heap.cost heap finalHeap = fun clock =>
        Clocks.single "heap_degree_scans" (maximum + 1).toNat clock +
          Clocks.single "heap_comparisons" comparisons clock := by
  obtain ⟨after, forest, comparisons, execution, ready, contents, unique, charged⟩ :=
    Algo2Lean.Fibonacci.rebuild_complete (snapshot heap layout) roots maximum represented buckets bound
  obtain ⟨finalHeap, finalLayout, effect, finalValid, observed, clocks⟩ :=
    realize_bucket_rebuild maximum (snapshot heap layout) after 0 roots.length comparisons
      execution heap queue layout valid rfl
  refine ⟨finalHeap, finalLayout, forest, comparisons, effect, ⟨finalValid, ?_⟩,
    contents, unique, charged, ?_⟩
  · rw [observed]
    exact ready
  · funext clock
    unfold Heap.cost
    rw [clocks]
    simp only [Int.sub_zero]
    omega



end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis


















theorem RebuildEffect.clocks_monotone {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {maximum degree : Int}
    (effect : RebuildEffect queue maximum heap layout degree after finalLayout) :
    ∀ clock, heap.clocks clock ≤ after.clocks clock := by
  induction effect with
  | done => intro clock; exact Nat.le_refl _
  | @step before after current final index inside rest ih =>
    intro clock
    have next := rebuild_clocks before queue current index clock
    have later := ih clock
    omega

/-- Consolidation starts from a finite pending-root ring, not a preselected
    global minimum. It returns a represented heap, preserves every entry and
    mark, and exposes the exact instrumented work of all three phases. -/
theorem consolidate_from_forest (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (forest : Algo2Lean.Fibonacci.Forest)
    (represented : Algo2Lean.Fibonacci.SplitRepresented (snapshot heap layout) forest [])
    (emptyTable : ∀ degree, heap.read layout.table degree < 0) :
    ∃ finalHeap finalLayout afterForest links scans comparisons,
      FibonacciHeap.consolidate.Call heap queue finalHeap () ∧
      ConsumeEffect queue heap layout (-1) finalHeap finalLayout forest.length links ∧
      QueueRep finalHeap queue finalLayout afterForest ∧
      afterForest.entries.Perm forest.entries ∧ afterForest.marks = forest.marks ∧
      links + afterForest.length = forest.length ∧
      afterForest.length ≤ 2 * forest.entries.length.log2 + 2 ∧
      scans ≤ 2 * forest.entries.length.log2 + 2 ∧ comparisons ≤ afterForest.length ∧
      Heap.cost heap finalHeap = fun clock =>
        Clocks.single "heap_root_scans" forest.length clock +
        Clocks.single "heap_comparisons" (links + comparisons) clock +
        Clocks.single "heap_links" links clock + Clocks.single "heap_degree_scans" scans clock := by
  have inputSize : (snapshot heap layout).size = forest.entries.length := by
    simpa only [List.append_nil] using represented.size
  have emptyBuckets := Algo2Lean.Fibonacci.Buckets.empty (state := snapshot heap layout) emptyTable
  have bound : Algo2Lean.Fibonacci.ScratchBound (snapshot heap layout) (-1) := by
    intro degree above
    exact emptyTable degree
  obtain ⟨after, buckets, maximum, links, pureRun, splitRep, table, maxBound, logarithmic,
      rootCount, finalSize, entries, marks⟩ :=
    represented.consume_roots emptyBuckets (-1) bound forest.entries.length inputSize (by omega)
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at rootCount entries marks
  obtain ⟨tailHeap, tailLayout, ready, observed, continuation, clocks⟩ :=
    realize_root_consumption _ _ _ _ _ _ pureRun heap queue layout valid rfl
  obtain ⟨finalHeap, finalLayout, afterForest, comparisons, rebuild, finalRep, permutation,
      unique, comparisonBound, rebuildCost⟩ :=
    rebuild_from_buckets tailHeap queue tailLayout ready buckets maximum
      (by rw [observed]; exact splitRep) (by rw [observed]; exact table)
      (by rw [observed]; exact maxBound)
  have effect := continuation finalHeap finalLayout rebuild
  have finalRootCount : links + afterForest.length = forest.length := by
    rw [permutation.length_eq]
    exact rootCount
  have rootsBound := table.roots_bound maxBound
  have maxNat : maximum.toNat ≤ 2 * forest.entries.length.log2 + 1 := by omega
  refine ⟨finalHeap, finalLayout, afterForest, links, (maximum + 1).toNat, comparisons,
    consolidate_effect_summary _ _ _ _ _ _ _ valid effect, effect, finalRep,
    (Algo2Lean.Fibonacci.Forest.entries_perm permutation).trans entries,
    (Algo2Lean.Fibonacci.Forest.marks_perm permutation).trans marks, finalRootCount,
    ?_, by omega, comparisonBound, ?_⟩
  · rw [permutation.length_eq]
    omega
  · funext clock
    have prefixClocks := clocks clock
    have suffix := congrFun rebuildCost clock
    have monotone := rebuild.clocks_monotone clock
    unfold Heap.cost at suffix ⊢
    by_cases clock = "heap_root_scans" <;> by_cases clock = "heap_comparisons" <;>
      by_cases clock = "heap_links" <;> by_cases clock = "heap_degree_scans" <;>
      simp_all [Clocks.single] <;> omega

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

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (forest : Algo2Lean.Fibonacci.Forest),
          Algo2Lean.Fibonacci.SplitRepresented (FibonacciModuleAnalysis.snapshot heap layout) forest
              List.nil.{0} →
            (∀ (degree : Int), LT.lt.{0} (heap.read layout.table degree) (0 : Int)) →
              Exists.{1} fun finalHeap =>
                Exists.{1} fun finalLayout =>
                  Exists.{1} fun afterForest =>
                    Exists.{1} fun links =>
                      Exists.{1} fun scans =>
                        Exists.{1} fun comparisons =>
                          Algo.fibonacci_heap.FibonacciHeap.consolidate.Call heap queue finalHeap () ∧
                            FibonacciModuleAnalysis.ConsumeEffect queue heap layout (-1 : Int) finalHeap
                                finalLayout (List.length.{0} forest) links ∧
                              FibonacciModuleAnalysis.QueueRep finalHeap queue finalLayout afterForest ∧
                                List.Perm.{0} afterForest.entries forest.entries ∧
                                  Eq.{1} afterForest.marks forest.marks ∧
                                    Eq.{1} (HAdd.hAdd.{0, 0, 0} links (List.length.{0} afterForest))
                                        (List.length.{0} forest) ∧
                                      LE.le.{0} (List.length.{0} afterForest)
                                          (HAdd.hAdd.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (2 : Nat)
                                              (List.length.{0} forest.entries).log2)
                                            (2 : Nat)) ∧
                                        LE.le.{0} scans
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0} (2 : Nat)
                                                (List.length.{0} forest.entries).log2)
                                              (2 : Nat)) ∧
                                          LE.le.{0} comparisons (List.length.{0} afterForest) ∧
                                            Eq.{1} (heap.cost finalHeap) fun clock =>
                                              HAdd.hAdd.{0, 0, 0}
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (Algo2LeanGenerated.Clocks.single "heap_root_scans"
                                                      (List.length.{0} forest) clock)
                                                    (Algo2LeanGenerated.Clocks.single "heap_comparisons"
                                                      (HAdd.hAdd.{0, 0, 0} links comparisons) clock))
                                                  (Algo2LeanGenerated.Clocks.single "heap_links" links
                                                    clock))
                                                (Algo2LeanGenerated.Clocks.single "heap_degree_scans"
                                                  scans clock) :=
  FibonacciModuleAnalysis.consolidate_from_forest
