-- Prove2me | solution 1 for FibonacciModuleAnalysis.QueueRep.insert
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:09.572666+00:00
-- url     : https://prove2.me/submissions/31eaff0e-95a2-4ac2-a745-a4a50e622b8c

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_add_root_summary


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

/-- Changes to a root's mark do not alter its internal heap order or rank history. -/
theorem Node.Ordered.withMark {node : Node} (ordered : node.Ordered) (marked : Bool) :
    (node.withMark marked).Ordered := by
  cases ordered with
  | make bounds children => exact .make bounds children

theorem Node.Ranked.withMark {node : Node} (ranked : node.Ranked) (marked : Bool) :
    (node.withMark marked).Ranked := by
  cases ranked with
  | make ordered children => exact .make ordered children



































/-- Content permutations preserve handle uniqueness; no pointer or key
    identity is lost during structural forest operations. -/
theorem Forest.Unique.of_entries_perm {before after : Forest} (unique : before.Unique)
    (contents : after.entries.Perm before.entries) : after.Unique :=
  ((contents.map Prod.fst).nodup_iff).mpr unique







/-- An unmarked root can be added when its handles are fresh for the forest. -/
theorem Forest.Valid.insert_root {forest : Forest} (valid : forest.Valid) (root : Node)
    (rootUnique : (root.entries.map Prod.fst).Nodup)
    (rootOrdered : root.Ordered) (rootRanked : root.Ranked)
    (fresh : ∀ vertex ∈ root.entries.map Prod.fst, vertex ∉ forest.entries.map Prod.fst) :
    (insertRoot root forest).Valid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Forest.Unique
    rw [Forest.insertRoot_entries, List.map_append]
    apply List.nodup_append.mpr
    refine ⟨rootUnique, valid.1, ?_⟩
    intro first inRoot second inForest same
    subst second
    exact fresh first inRoot inForest
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact rootOrdered.withMark false
    · exact valid.2.1 node old
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · exact rootRanked.withMark false
    · exact valid.2.2.1 node old
  · intro node member
    rcases List.mem_cons.mp member with rfl | old
    · rfl
    · exact valid.2.2.2 node old







































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

theorem Stored.root_present {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) : state.present node.vertex = 1 := by
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

theorem Represented.empty_iff {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) : state.minimum < 0 ↔ forest = [] := by
  constructor
  · intro negative
    by_cases empty : forest = []
    · exact empty
    · have bound := represented.minimum_key empty
      omega
  · intro empty
    rcases represented.minimum with ⟨_, pointer⟩ | ⟨root, member, _⟩
    · omega
    · simp [empty] at member

theorem Represented.empty_presence {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (empty : forest = []) :
    ∀ vertex, state.present vertex = 0 := by
  intro vertex
  have absent := represented.presence vertex
  simp [empty, Forest.entries] at absent
  exact absent









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

/-- A cyclic choice of the first root does not alter the represented snapshot. -/
theorem Represented.rotate {state : Snapshot} {front back : Forest}
    (represented : Represented state (front ++ back)) : Represented state (back ++ front) := by
  have permutation : (back ++ front).Perm (front ++ back) := List.perm_append_comm
  have contents := permutation.flatMap_right Node.entries
  refine ⟨represented.valid.perm permutation, ?_, ?_, ?_, ?_, ?_, ?_, represented.scratch⟩
  · simpa only [List.map_append] using (Rings.RingOrEmpty.rotate_append (front.map Node.vertex) (back.map Node.vertex) (by simpa only [List.map_append] using represented.roots))
  · intro root member
    exact represented.stored root (permutation.mem_iff.mp member)
  · intro vertex key member
    exact represented.nonnegative vertex key (contents.mem_iff.mp member)
  · intro vertex
    rw [represented.presence]
    exact exists_congr (fun _ => contents.mem_iff.symm)
  · exact represented.size.trans (congrArg Int.ofNat contents.length_eq.symm)
  · rcases represented.minimum with ⟨empty, pointer⟩ | ⟨root, member, pointer, least⟩
    · left
      exact ⟨by simpa only [List.append_eq_nil_iff, and_comm] using empty, pointer⟩
    · exact Or.inr ⟨root, permutation.mem_iff.mpr member, pointer,
        fun other member => least other (permutation.mem_iff.mp member)⟩



private theorem singleton_valid (vertex key : Int) : Forest.Valid [Node.make vertex key false []] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Forest.Unique, Forest.entries, Node.entries]
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact Node.Ordered.make (by simp) (by simp)
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact Node.Ranked.make (by trivial) (by simp)
  · simp [Forest.RootsUnmarked, Node.marked]

private theorem singleton_stored (state : Snapshot) (vertex key : Int) :
    Stored (state.insertSingleton vertex key) (-1) (Node.make vertex key false []) := by
  apply Stored.node <;> simp [Snapshot.insertSingleton, Rings.write, Rings.RingOrEmpty]

/-- The first insertion works for arbitrary unused array cells. -/
theorem Represented.insert_empty {state : Snapshot} (represented : Represented state [])
    (vertex key : Int) (nonnegative : 0 ≤ vertex) :
    Represented (state.insertSingleton vertex key) [Node.make vertex key false []] := by
  have empty := represented.empty_iff.mpr rfl
  have absent := represented.empty_presence rfl
  refine ⟨singleton_valid vertex key, ?_, ?_, ?_, ?_, ?_, ?_, represented.scratch⟩
  · apply Or.inr
    apply Rings.singleton_ring <;> simp [Snapshot.insertSingleton, empty, Node.vertex]
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact singleton_stored state vertex key
  · intro value weight member
    simp [Forest.entries, Node.entries] at member
    exact member.1 ▸ nonnegative
  · intro value
    simp [Snapshot.insertSingleton, Rings.write, Forest.entries, Node.entries, absent]
  · have zero : state.size = 0 := by simpa [Forest.entries] using represented.size
    simp [Snapshot.insertSingleton, Forest.entries, Node.entries, zero]
  · right
    refine ⟨Node.make vertex key false [], by simp, ?_, ?_⟩
    · simp [Snapshot.insertSingleton, empty, Node.vertex]
    · simp [Node.key]

/-- An absent address cannot alias any active entry. -/
theorem Represented.fresh {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int} (absent : state.present vertex = 0) :
    vertex ∉ forest.entries.map Prod.fst := by
  intro member
  obtain ⟨⟨value, key⟩, inside, same⟩ := List.mem_map.mp member
  change value = vertex at same
  subst value
  have present := (represented.entry inside).2
  omega

theorem Represented.root_parent {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex : Int} (member : vertex ∈ forest.map Node.vertex) :
    state.parents vertex = -1 := by
  obtain ⟨root, inForest, same⟩ := List.mem_map.mp member
  rw [← same]
  exact (represented.stored root inForest).root_parent

/-- Inserting at the minimum only rewires old root pointers. Metadata and all
    internal child rings are preserved for every existing tree. -/
theorem Represented.insert_stored {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (absent : state.present vertex = 0) {root : Node} (member : root ∈ forest) :
    Stored (state.insertSingleton vertex key) (-1) root := by
  have noAlias (value weight : Int) (inside : (value, weight) ∈ root.entries) : value ≠ vertex := by
    have present := (represented.stored root member).entries value weight inside
    intro same
    subst value
    omega
  apply (represented.stored root member).frame_roots
  · intro value weight inside
    exact represented.nonnegative value weight (List.mem_flatMap.mpr ⟨root, member, inside⟩)
  · intro value weight inside
    have different := noAlias value weight inside
    constructor <;> simp [Snapshot.insertSingleton, Rings.write, different]
  · intro value active nonroot
    have different : value ≠ vertex := by intro same; subst value; omega
    by_cases empty : state.minimum < 0
    · simp [Snapshot.insertSingleton, empty, Rings.write, different]
    · have nonempty : forest ≠ [] := fun same => empty (represented.empty_iff.mpr same)
      obtain ⟨least, leastMember, pointer, _⟩ := represented.minimum.resolve_left
        (fun same => nonempty same.1)
      have minimumMember : state.minimum ∈ forest.map Node.vertex := by
        rw [pointer]
        exact List.mem_map.mpr ⟨least, leastMember, rfl⟩
      have ring : Rings.Ring state.left state.right (forest.map Node.vertex) := by
        rcases represented.roots with impossible | ring
        · simp only [List.map_eq_nil_iff] at impossible
          exact False.elim (nonempty impossible)
        · exact ring
      have successorMember := (ring.neighbors minimumMember).2
      have minimumParent := represented.root_parent minimumMember
      have successorParent := represented.root_parent successorMember
      have notMinimum : value ≠ state.minimum := by intro same; subst value; omega
      have notSuccessor : value ≠ state.right state.minimum := by intro same; rw [same] at nonroot; omega
      simp [Snapshot.insertSingleton, empty, Rings.insertAfterLeft, Rings.insertAfterRight,
        Rings.write, different, notMinimum, notSuccessor]

/-- If the abstract root list starts at the minimum, insertion has the exact
    logical order used by the source's `add_root`: old minimum, new node, rest. -/
theorem Represented.insert_after_minimum {state : Snapshot} {root : Node} {rest : Forest}
    (represented : Represented state (root :: rest)) {vertex key : Int}
    (nonnegative : 0 ≤ vertex) (absent : state.present vertex = 0)
    (minimum : state.minimum = root.vertex) :
    Represented (state.insertSingleton vertex key) (root :: Node.make vertex key false [] :: rest) := by
  let singleton := Node.make vertex key false []
  change Represented (state.insertSingleton vertex key) (root :: singleton :: rest)
  have contents : Forest.entries (root :: singleton :: rest) =
      root.entries ++ (vertex, key) :: rest.entries := by simp [Forest.entries, singleton, Node.entries]
  have oldNonempty : root :: rest ≠ [] := by simp
  have notEmpty : ¬state.minimum < 0 := fun negative => oldNonempty (represented.empty_iff.mp negative)
  have vertexFresh := represented.fresh absent
  have rootFresh : vertex ∉ (root :: rest).map Node.vertex := by
    intro member
    obtain ⟨node, member, same⟩ := List.mem_map.mp member
    apply vertexFresh
    exact List.mem_map.mpr ⟨(node.vertex, node.key), List.mem_flatMap.mpr ⟨node, member, node.root_entry⟩, same⟩
  have singletonValid := singleton_valid vertex key
  have insertedValid : Forest.Valid (singleton :: root :: rest) := by
    have result := represented.valid.insert_root singleton
      (by simp [singleton, Node.entries])
      (singletonValid.2.1 singleton (by simp [singleton]))
      (singletonValid.2.2.1 singleton (by simp [singleton]))
      (by
        intro value member
        have same : value = vertex := by simpa [singleton, Node.entries] using member
        simpa only [same] using vertexFresh)
    simpa [Forest.insertRoot, singleton, Node.withMark] using! result
  have oldRing : Rings.Ring state.left state.right (root.vertex :: rest.map Node.vertex) := by
    rcases represented.roots with impossible | ring
    · simp at impossible
    · exact ring
  have minimumKey : state.keys state.minimum = root.key := minimum ▸ (represented.stored root (by simp)).root_key
  have least : ∀ other ∈ root :: rest, root.key ≤ other.key := by
    have global := (represented.minimum_key oldNonempty).2.2
    intro other member
    have active := (represented.stored other member).root_present
    have bound := global other.vertex (by omega)
    rw [minimumKey, (represented.stored other member).root_key] at bound
    exact bound
  refine ⟨insertedValid.perm (List.Perm.swap singleton root rest), ?_, ?_, ?_, ?_, ?_, ?_, represented.scratch⟩
  · apply Or.inr
    dsimp only [Snapshot.insertSingleton]
    rw [if_neg notEmpty, if_neg notEmpty]
    simpa only [minimum, List.map_cons, singleton, Node.vertex] using oldRing.insert_after rootFresh
  · intro node member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact represented.insert_stored absent (by simp)
    · exact singleton_stored state vertex key
    · exact represented.insert_stored absent (by simp [member])
  · intro value weight member
    simp only [contents, List.mem_append, List.mem_cons, Prod.mk.injEq] at member
    rcases member with member | ⟨rfl, rfl⟩ | member
    · exact represented.nonnegative value weight (by simpa [Forest.entries] using Or.inl member)
    · exact nonnegative
    · exact represented.nonnegative value weight (by simpa [Forest.entries] using Or.inr member)
  · intro value
    simp only [Snapshot.insertSingleton, Rings.write, contents, List.mem_append, List.mem_cons, Prod.mk.injEq]
    by_cases same : value = vertex
    · simp [same]
      exact ⟨key, Or.inr (Or.inl rfl)⟩
    · simp only [same, ↓reduceIte, false_and, false_or]
      simpa [Forest.entries, List.mem_append, exists_or] using represented.presence value
  · have size := represented.size
    simp only [Forest.entries, List.flatMap_cons, List.length_append] at size
    change state.size + 1 = Int.ofNat (Forest.entries (root :: singleton :: rest)).length
    rw [contents]
    simp only [List.length_append, List.length_cons, Forest.entries, Int.ofNat_eq_natCast]
    omega
  · right
    by_cases better : key < state.keys state.minimum
    · refine ⟨singleton, by simp, ?_, ?_⟩
      · simp only [Snapshot.insertSingleton, if_neg notEmpty, if_pos better, singleton, Node.vertex]
      · intro other member
        simp only [List.mem_cons] at member
        rcases member with same | same | member
        · subst other
          change key ≤ root.key
          rw [minimumKey] at better
          omega
        · subst other
          exact Int.le_refl _
        · have bound := least other (by simp [member])
          change key ≤ other.key
          rw [minimumKey] at better
          omega
    · refine ⟨root, by simp, ?_, ?_⟩
      · change (if state.minimum < 0 then vertex else if key < state.keys state.minimum then vertex else state.minimum) = root.vertex
        rw [if_neg notEmpty, if_neg better, minimum]
      · intro other member
        simp only [List.mem_cons] at member
        rcases member with same | same | member
        · subst other
          exact Int.le_refl _
        · subst other
          change root.key ≤ key
          rw [minimumKey] at better
          omega
        · exact least other (by simp [member])

/-- A fresh insertion preserves the complete representation, adds exactly the
    supplied entry, and increases the root count by one without adding marks. -/
theorem Represented.insert_singleton {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (nonnegative : 0 ≤ vertex) (absent : state.present vertex = 0) :
    ∃ afterForest, Represented (state.insertSingleton vertex key) afterForest ∧
      afterForest.entries.Perm ((vertex, key) :: forest.entries) ∧
      afterForest.length = forest.length + 1 ∧ afterForest.marks = forest.marks := by
  by_cases empty : forest = []
  · subst forest
    refine ⟨[Node.make vertex key false []], represented.insert_empty vertex key nonnegative, ?_, rfl, ?_⟩
    · simp [Forest.entries, Node.entries]
    · simp [Forest.marks, Node.marks]
  · obtain ⟨root, member, pointer, _⟩ := represented.minimum.resolve_left (fun impossible => empty impossible.1)
    obtain ⟨front, back, located⟩ := List.mem_iff_append.mp member
    subst forest
    have rotated : Represented state (root :: (back ++ front)) := represented.rotate
    have after := rotated.insert_after_minimum (key := key) nonnegative absent pointer
    refine ⟨root :: Node.make vertex key false [] :: (back ++ front), after, ?_, ?_, ?_⟩
    · have reordered : (root :: (back ++ front)).Perm (front ++ root :: back) := by
        simpa only [List.cons_append] using (List.perm_append_comm (l₁ := root :: back) (l₂ := front))
      have entries := reordered.flatMap_right Node.entries
      apply List.Perm.trans _ (entries.cons (vertex, key))
      simp [Forest.entries, Node.entries]
    · simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · simp [Forest.marks, Node.marks, List.sum_append_nat, Nat.add_comm, Nat.add_assoc]
























































































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










theorem QueueRep.minimum {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (nonempty : forest ≠ []) :
    0 ≤ layout.minimum ∧ heap.read layout.present layout.minimum = 1 ∧
      ∀ vertex, heap.read layout.present vertex ≠ 0 →
        heap.read layout.keys layout.minimum ≤ heap.read layout.keys vertex :=
  rep.represented.minimum_key nonempty

theorem QueueRep.empty_iff {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest) :
    layout.minimum < 0 ↔ forest = [] := rep.represented.empty_iff


end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

theorem Layout.Valid.set_size (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (size : Int) :
    { layout with size := size }.Valid (set_FibonacciHeap_size heap queue size) queue := by
  constructor
  · simpa [set_FibonacciHeap_size, is_FibonacciHeap] using valid.object
  · simpa [field_FibonacciHeap_keys, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readKeys
  · simpa [field_FibonacciHeap_parents, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readParents
  · simpa [field_FibonacciHeap_children, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readChildren
  · simpa [field_FibonacciHeap_left, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readLeft
  · simpa [field_FibonacciHeap_right, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readRight
  · simpa [field_FibonacciHeap_degrees, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readDegrees
  · simpa [field_FibonacciHeap_marks, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readMarks
  · simpa [field_FibonacciHeap_present, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readPresent
  · simpa [field_FibonacciHeap_table, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readTable
  · simpa [field_FibonacciHeap_minimum, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readMinimum
  · exact field_FibonacciHeap_size_set heap queue size valid.object
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











theorem insertion_header_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    { layout with size := layout.size + 1 }.Valid
      (insertionHeaderHeap heap queue layout vertex key) queue := by
  apply Layout.Valid.set_size
  repeat apply Layout.Valid.write
  exact Layout.Valid.tick _ _ _ valid _ _

theorem insertion_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionLayout heap queue layout vertex key).Valid
      (insertionHeap heap queue layout vertex key) queue := by
  apply add_root_layout
  exact insertion_header_layout heap queue layout valid vertex key

/-- A new handle is initialized once, then reuses the independent root insertion proof. -/
theorem push_insert_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (absent : heap.read layout.present vertex = 0) :
    FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
      (insertionHeap heap queue layout vertex key) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc44 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc43 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc42_true _ _ _
    (by simp [valid.readPresent, absent]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc41 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc40 _ _ _
    (by simp [valid.readChildren, valid.childrenAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc39 _ _ _
    (by simp [valid.readDegrees, valid.degreesAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc38 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc37 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc36 _ _ _
    (by simp [valid.readSize]))
  simp only [keys_tick, children_write, children_tick, degrees_write,
    degrees_tick, present_write, present_tick, size_write, size_tick,
    valid.readKeys, valid.readChildren, valid.readDegrees, valid.readPresent,
    valid.readSize, Option.getD_some]
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc35 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc34 _ _ _ valid.object)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc33 _ _ _)
  have ready := insertion_header_layout heap queue layout valid vertex key
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc32 _ _ _ ready.object)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc31 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc30 _ _ _)
  apply Reaches.trans ((add_root_summary _ _ _ ready vertex).2 _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc29 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc28 _ _ _)

























theorem insertion_size (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex key : Int) :
    (insertionLayout heap queue layout vertex key).size = layout.size + 1 := by
  unfold insertionLayout addRootLayout
  split
  · rfl
  · dsimp only
    split <;> rfl



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

theorem insertion_read_keys (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.keys =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.keys) vertex key := by
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
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, keys_parents,
        keys_children, keys_left, keys_right, keys_degrees, keys_marks, keys_present, eq_self,
        true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, keys_parents, keys_children, keys_left, keys_right,
        keys_degrees, keys_marks, keys_present, eq_self, true_and, false_and, if_false]

theorem insertion_read_parents (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.parents =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.parents) vertex (-1) := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have parents_keys : layout.parents ≠ layout.keys := Ne.symm (different.1.1)
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, parents_keys,
        parents_children, parents_left, parents_right, parents_degrees, parents_marks,
        parents_present, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, parents_keys, parents_children, parents_left,
        parents_right, parents_degrees, parents_marks, parents_present, eq_self, true_and,
        false_and, if_false]

theorem insertion_read_children (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.children =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.children) vertex (-1) := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have children_keys : layout.children ≠ layout.keys := Ne.symm (different.1.2.1)
  have children_parents : layout.children ≠ layout.parents := Ne.symm (different.2.1.1)
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, children_keys,
        children_parents, children_left, children_right, children_degrees, children_marks,
        children_present, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, children_keys, children_parents, children_left,
        children_right, children_degrees, children_marks, children_present, eq_self, true_and,
        false_and, if_false]

theorem insertion_read_left (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.left =
      if layout.minimum < 0 then Algo2Lean.Fibonacci.Rings.write (heap.read layout.left) vertex vertex else Algo2Lean.Fibonacci.Rings.insertAfterLeft (heap.read layout.left) (heap.read layout.right) layout.minimum vertex := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have left_keys : layout.left ≠ layout.keys := Ne.symm (different.1.2.2.1)
  have left_parents : layout.left ≠ layout.parents := Ne.symm (different.2.1.2.1)
  have left_children : layout.left ≠ layout.children := Ne.symm (different.2.2.1.1)
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_keys : layout.right ≠ layout.keys := Ne.symm (different.1.2.2.2.1)
  have right_children : layout.right ≠ layout.children := Ne.symm (different.2.2.1.2.1)
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_parents : layout.right ≠ layout.parents := Ne.symm (different.2.1.2.2.1)
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, left_keys,
        left_parents, left_children, left_right, left_degrees, left_marks, left_present, eq_self,
        true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, Algo2Lean.Fibonacci.Rings.insertAfterLeft, left_keys,
        left_parents, left_children, left_right, left_degrees, left_marks, left_present, right_keys,
        right_children, right_degrees, right_present, right_parents, right_marks, eq_self, true_and,
        false_and, if_false]

theorem insertion_read_right (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.right =
      if layout.minimum < 0 then Algo2Lean.Fibonacci.Rings.write (heap.read layout.right) vertex vertex else Algo2Lean.Fibonacci.Rings.insertAfterRight (heap.read layout.right) layout.minimum vertex := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have right_keys : layout.right ≠ layout.keys := Ne.symm (different.1.2.2.2.1)
  have right_parents : layout.right ≠ layout.parents := Ne.symm (different.2.1.2.2.1)
  have right_children : layout.right ≠ layout.children := Ne.symm (different.2.2.1.2.1)
  have right_left : layout.right ≠ layout.left := Ne.symm (different.2.2.2.1.1)
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, right_keys,
        right_parents, right_children, right_left, right_degrees, right_marks, right_present,
        eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, Algo2Lean.Fibonacci.Rings.insertAfterRight, right_keys,
        right_parents, right_children, right_left, right_degrees, right_marks, right_present,
        eq_self, true_and, false_and, if_false]

theorem insertion_read_degrees (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.degrees =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.degrees) vertex 0 := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have degrees_keys : layout.degrees ≠ layout.keys := Ne.symm (different.1.2.2.2.2.1)
  have degrees_parents : layout.degrees ≠ layout.parents := Ne.symm (different.2.1.2.2.2.1)
  have degrees_children : layout.degrees ≠ layout.children := Ne.symm (different.2.2.1.2.2.1)
  have degrees_left : layout.degrees ≠ layout.left := Ne.symm (different.2.2.2.1.2.1)
  have degrees_right : layout.degrees ≠ layout.right := Ne.symm (different.2.2.2.2.1.1)
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, degrees_keys,
        degrees_parents, degrees_children, degrees_left, degrees_right, degrees_marks,
        degrees_present, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, degrees_keys, degrees_parents, degrees_children,
        degrees_left, degrees_right, degrees_marks, degrees_present, eq_self, true_and, false_and,
        if_false]

theorem insertion_read_marks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.marks =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.marks) vertex 0 := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have marks_keys : layout.marks ≠ layout.keys := Ne.symm (different.1.2.2.2.2.2.1)
  have marks_parents : layout.marks ≠ layout.parents := Ne.symm (different.2.1.2.2.2.2.1)
  have marks_children : layout.marks ≠ layout.children := Ne.symm (different.2.2.1.2.2.2.1)
  have marks_left : layout.marks ≠ layout.left := Ne.symm (different.2.2.2.1.2.2.1)
  have marks_right : layout.marks ≠ layout.right := Ne.symm (different.2.2.2.2.1.2.1)
  have marks_degrees : layout.marks ≠ layout.degrees := Ne.symm (different.2.2.2.2.2.1.1)
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, marks_keys,
        marks_parents, marks_children, marks_left, marks_right, marks_degrees, marks_present,
        eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, marks_keys, marks_parents, marks_children, marks_left,
        marks_right, marks_degrees, marks_present, eq_self, true_and, false_and, if_false]

theorem insertion_read_present (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.present =
      Algo2Lean.Fibonacci.Rings.write (heap.read layout.present) vertex 1 := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have present_keys : layout.present ≠ layout.keys := Ne.symm (different.1.2.2.2.2.2.2.1)
  have present_parents : layout.present ≠ layout.parents := Ne.symm (different.2.1.2.2.2.2.2.1)
  have present_children : layout.present ≠ layout.children := Ne.symm (different.2.2.1.2.2.2.2.1)
  have present_left : layout.present ≠ layout.left := Ne.symm (different.2.2.2.1.2.2.2.1)
  have present_right : layout.present ≠ layout.right := Ne.symm (different.2.2.2.2.1.2.2.1)
  have present_degrees : layout.present ≠ layout.degrees := Ne.symm (different.2.2.2.2.2.1.2.1)
  have present_marks : layout.present ≠ layout.marks := Ne.symm (different.2.2.2.2.2.2.1.1)
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Rings.write, present_keys,
        present_parents, present_children, present_left, present_right, present_degrees,
        present_marks, eq_self, true_and, false_and, if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
        Algo2Lean.Fibonacci.Rings.write, present_keys, present_parents, present_children,
        present_left, present_right, present_degrees, present_marks, eq_self, true_and, false_and,
        if_false]

theorem insertion_read_table (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    (insertionHeap heap queue layout vertex key).read layout.table =
      heap.read layout.table := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have table_keys : layout.table ≠ layout.keys := Ne.symm (different.1.2.2.2.2.2.2.2)
  have table_parents : layout.table ≠ layout.parents := Ne.symm (different.2.1.2.2.2.2.2.2)
  have table_children : layout.table ≠ layout.children := Ne.symm (different.2.2.1.2.2.2.2.2)
  have table_left : layout.table ≠ layout.left := Ne.symm (different.2.2.2.1.2.2.2.2)
  have table_right : layout.table ≠ layout.right := Ne.symm (different.2.2.2.2.1.2.2.2)
  have table_degrees : layout.table ≠ layout.degrees := Ne.symm (different.2.2.2.2.2.1.2.2)
  have table_marks : layout.table ≠ layout.marks := Ne.symm (different.2.2.2.2.2.2.1.2)
  have table_present : layout.table ≠ layout.present := Ne.symm (different.2.2.2.2.2.2.2)
  unfold insertionHeap addRootHeap
  dsimp only
  split
  · rename_i empty
    funext index
    simp only [insertionHeaderHeap, rootHeaderHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read,
        Heap.write, Heap.writeField, Heap.tick, table_keys, table_parents, table_children,
        table_left, table_right, table_degrees, table_marks, table_present, eq_self, false_and,
        if_false]
  · rename_i empty
    split <;> funext index <;>
      simp only [insertionHeaderHeap, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
        set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick, table_keys,
        table_parents, table_children, table_left, table_right, table_degrees, table_marks,
        table_present, eq_self, false_and, if_false]


theorem insertion_minimum (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (freshMinimum : layout.minimum < 0 ∨ vertex ≠ layout.minimum) :
    (insertionLayout heap queue layout vertex key).minimum =
      if layout.minimum < 0 then vertex
      else if key < heap.read layout.keys layout.minimum then vertex else layout.minimum := by
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
  unfold insertionLayout addRootLayout
  dsimp only
  by_cases empty : layout.minimum < 0
  · simp [empty]
  · have fresh : layout.minimum ≠ vertex := Ne.symm (freshMinimum.resolve_left empty)
    simp [empty, insertionHeaderHeap, rootHeaderHeap, insertRingHeap,
      set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField, Heap.tick,
      keys_parents, keys_children, keys_left, keys_right, keys_degrees, keys_marks,
      keys_present, fresh]
    split <;> rfl

theorem insertion_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (freshMinimum : layout.minimum < 0 ∨ vertex ≠ layout.minimum) :
    snapshot (insertionHeap heap queue layout vertex key)
      (insertionLayout heap queue layout vertex key) =
        (snapshot heap layout).insertSingleton vertex key := by
  have fields := add_root_layout_refs (insertionHeaderHeap heap queue layout vertex key)
    {layout with size := layout.size + 1} vertex
  change (insertionLayout heap queue layout vertex key).refs = layout.refs at fields
  simp only [Layout.refs, List.cons.injEq] at fields
  apply snapshot_ext
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).keys = _
    rw [fields.1]
    exact insertion_read_keys heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).parents = _
    rw [fields.2.1]
    exact insertion_read_parents heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).children = _
    rw [fields.2.2.1]
    exact insertion_read_children heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).left = _
    rw [fields.2.2.2.1]
    exact insertion_read_left heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).right = _
    rw [fields.2.2.2.2.1]
    exact insertion_read_right heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).degrees = _
    rw [fields.2.2.2.2.2.1]
    exact insertion_read_degrees heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).marks = _
    rw [fields.2.2.2.2.2.2.1]
    exact insertion_read_marks heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).present = _
    rw [fields.2.2.2.2.2.2.2.1]
    exact insertion_read_present heap queue layout valid vertex key
  · change (insertionHeap heap queue layout vertex key).read
      (insertionLayout heap queue layout vertex key).table = _
    rw [fields.2.2.2.2.2.2.2.2.1]
    exact insertion_read_table heap queue layout valid vertex key
  · exact insertion_minimum heap queue layout valid vertex key freshMinimum
  · exact insertion_size heap queue layout vertex key

/-- Fresh insertion preserves the complete finite-forest representation and
    inserts precisely the supplied key/handle pair. -/
theorem QueueRep.insert {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (vertex key : Int) (nonnegative : 0 ≤ vertex) (absent : heap.read layout.present vertex = 0) :
    ∃ afterForest,
      FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
        (insertionHeap heap queue layout vertex key) () ∧
      QueueRep (insertionHeap heap queue layout vertex key) queue
        (insertionLayout heap queue layout vertex key) afterForest ∧
      afterForest.entries.Perm ((vertex, key) :: forest.entries) ∧
      afterForest.length = forest.length + 1 ∧ afterForest.marks = forest.marks := by
  have fresh : layout.minimum < 0 ∨ vertex ≠ layout.minimum := by
    by_cases empty : layout.minimum < 0
    · exact Or.inl empty
    · right
      have nonempty : forest ≠ [] := by intro same; exact empty (rep.empty_iff.mpr same)
      have minimum := (rep.minimum nonempty).2.1
      intro same
      rw [same, minimum] at absent
      contradiction
  obtain ⟨afterForest, represented, entries, roots, marks⟩ :=
    rep.represented.insert_singleton (key := key) nonnegative absent
  refine ⟨afterForest, push_insert_summary heap queue layout rep.layoutValid vertex key absent,
    ⟨insertion_layout heap queue layout rep.layoutValid vertex key, ?_⟩, entries, roots, marks⟩
  rw [insertion_snapshot heap queue layout rep.layoutValid vertex key fresh]
  exact represented



































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

set_option autoImplicit false
theorem solution :
    ∀ {heap : Algo2LeanGenerated.Heap}
      {queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap}
      {layout : FibonacciModuleAnalysis.Layout} {forest : Algo2Lean.Fibonacci.Forest},
      FibonacciModuleAnalysis.QueueRep heap queue layout forest →
        ∀ (vertex key : Int),
          LE.le.{0} (0 : Int) vertex →
            Eq.{1} (heap.read layout.present vertex) (0 : Int) →
              Exists.{1} fun afterForest =>
                Algo.fibonacci_heap.FibonacciHeap.push_or_decrease.Call heap
                    (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key))
                    (FibonacciModuleAnalysis.insertionHeap heap queue layout vertex key) () ∧
                  FibonacciModuleAnalysis.QueueRep
                      (FibonacciModuleAnalysis.insertionHeap heap queue layout vertex key) queue
                      (FibonacciModuleAnalysis.insertionLayout heap queue layout vertex key)
                      afterForest ∧
                    List.Perm.{0} afterForest.entries
                        (List.cons.{0} (Prod.mk.{0, 0} vertex key) forest.entries) ∧
                      Eq.{1} (List.length.{0} afterForest)
                          (HAdd.hAdd.{0, 0, 0} (List.length.{0} forest) (1 : Nat)) ∧
                        Eq.{1} afterForest.marks forest.marks :=
  FibonacciModuleAnalysis.QueueRep.insert
