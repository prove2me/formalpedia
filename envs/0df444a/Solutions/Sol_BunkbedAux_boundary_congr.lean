-- Prove2me | solution 1 for BunkbedAux.boundary_congr
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:59:10.685645+00:00
-- url     : https://prove2.me/submissions/c3e68a4d-3b8f-4812-b779-194ae8dab82d

import Definitions.Def_BunkbedPercolation

/-!
# Connectivity in a union of parts depends only on the boundary partition

Let `S : iota → Finset (Sym2 V)` be a family of edge sets whose *supports* meet only inside a
distinguished set `B : Finset V` of **boundary** vertices: every vertex covered by an edge of
`S i` which is not in `B` is covered by no edge of any other part (`hsupp` below).

Then, for boundary vertices `x y ∈ B`, whether `x` and `y` are connected in the union
`ofEdges (univ.biUnion S)` depends on the parts *only* through the relation each part induces on
`B`, namely `{(p, q) ∈ B × B | (ofEdges (S i)).Reachable p q}`.  This is the substitution
principle that lets one replace a gadget by any other gadget realising the same boundary
partition distribution.

The proof is by walk induction with the invariant `Good` below: a walk in the union may change
part only at a boundary vertex, because non-boundary vertices are private to a single part.
No graph homomorphism between the two unions is needed (in general none exists).
-/

open Bunkbed Finset SimpleGraph

set_option linter.unusedSectionVars false

namespace SubBoundary

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-! ## Elementary facts about `ofEdges` -/

/-- If `u` is reachable from some *other* vertex, then `u` is covered by an edge. -/
lemma exists_edge_of_reachable_ne {T : Finset (Sym2 V)} {b u : V}
    (h : (ofEdges T).Reachable b u) (hne : b ≠ u) : ∃ f ∈ T, u ∈ f := by
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => exact absurd rfl hne
  | cons hadj q =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact ⟨_, Finset.mem_coe.1 hadj.1, by simp⟩

/-- Reachability inside one part gives reachability in the union. -/
lemma reachable_union (S : iota → Finset (Sym2 V)) (i : iota) {p q : V}
    (h : (ofEdges (S i)).Reachable p q) :
    (ofEdges (univ.biUnion S)).Reachable p q :=
  h.mono (fromEdgeSet_mono
    (Finset.coe_subset.2 (Finset.subset_biUnion_of_mem S (mem_univ i))))

/-- An edge of the union is an edge of some part. -/
lemma adj_union_part {S : iota → Finset (Sym2 V)} {u v : V}
    (h : (ofEdges (univ.biUnion S)).Adj u v) :
    ∃ i, (ofEdges (S i)).Adj u v ∧ s(u, v) ∈ S i := by
  rw [SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨hmem, hne⟩ := h
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hmem)
  exact ⟨i, (SimpleGraph.fromEdgeSet_adj _).2 ⟨Finset.mem_coe.2 hi, hne⟩, hi⟩

/-! ## The walk invariant -/

/-- The invariant carried along a walk in `ofEdges (univ.biUnion S)` starting at `x`:
the current vertex `v` is reached from `x` by first travelling in the *new* union
`univ.biUnion S'` to a boundary vertex `b`, and then travelling inside a **single** part of the
*old* family `S`. -/
def Good (S S' : iota → Finset (Sym2 V)) (B : Finset V) (x v : V) : Prop :=
  ∃ b ∈ B, (ofEdges (univ.biUnion S')).Reachable x b ∧
    (b = v ∨ ∃ i, (ofEdges (S i)).Reachable b v)

/-- The invariant is preserved by one step of a walk in the union. -/
lemma good_step {S S' : iota → Finset (Sym2 V)} {B : Finset V}
    (hsame : ∀ i, ∀ p ∈ B, ∀ q ∈ B,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ B → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x u v : V} (hu : Good S S' B x u)
    (hadj : (ofEdges (univ.biUnion S)).Adj u v) : Good S S' B x v := by
  obtain ⟨b, hbB, hxb, hbu⟩ := hu
  obtain ⟨i, hadji, hi⟩ := adj_union_part hadj
  by_cases huB : u ∈ B
  · -- we may restart the "inside one part" leg at the boundary vertex `u`
    refine ⟨u, huB, ?_, Or.inr ⟨i, hadji.reachable⟩⟩
    rcases hbu with rfl | ⟨j, hj⟩
    · exact hxb
    · exact hxb.trans (reachable_union S' j (hsame j b hbB u huB hj))
  · -- `u` is not a boundary vertex, so it is private to the part `i` containing `s(u, v)`
    rcases hbu with rfl | ⟨j, hj⟩
    · exact absurd hbB huB
    · have hbne : b ≠ u := by rintro rfl; exact huB hbB
      have hji : j = i := by
        by_contra hjne
        obtain ⟨f, hf, huf⟩ := exists_edge_of_reachable_ne hj hbne
        exact hsupp i s(u, v) hi u (by simp) huB j hjne f hf huf
      have hj' : (ofEdges (S i)).Reachable b u := by rw [← hji]; exact hj
      exact ⟨b, hbB, hxb, Or.inr ⟨i, hj'.trans hadji.reachable⟩⟩

/-- The invariant is preserved along a whole walk in the union. -/
lemma good_transport {S S' : iota → Finset (Sym2 V)} {B : Finset V}
    (hsame : ∀ i, ∀ p ∈ B, ∀ q ∈ B,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ B → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x u v : V} (W : (ofEdges (univ.biUnion S)).Walk u v) :
    Good S S' B x u → Good S S' B x v := by
  induction W with
  | nil => exact id
  | cons hadj _ ih => exact fun h => ih (good_step hsame hsupp h hadj)

/-! ## One direction of the substitution principle -/

/-- **One direction.**  If each part of `S` induces on the boundary `B` a sub-relation of the
relation induced by the corresponding part of `S'`, and non-boundary vertices of each part of `S`
are private to that part, then boundary connections of `univ.biUnion S` are boundary connections
of `univ.biUnion S'`.  (Note that no support hypothesis on `S'` is needed here.) -/
theorem reachable_of_reachable {S S' : iota → Finset (Sym2 V)} {B : Finset V}
    (hsame : ∀ i, ∀ p ∈ B, ∀ q ∈ B,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ B → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x y : V} (hx : x ∈ B) (hy : y ∈ B)
    (h : (ofEdges (univ.biUnion S)).Reachable x y) :
    (ofEdges (univ.biUnion S')).Reachable x y := by
  obtain ⟨W⟩ := h
  obtain ⟨b, hbB, hxb, hby⟩ :=
    good_transport hsame hsupp W ⟨x, hx, SimpleGraph.Reachable.refl x, Or.inl rfl⟩
  rcases hby with rfl | ⟨j, hj⟩
  · exact hxb
  · exact hxb.trans (reachable_union S' j (hsame j b hbB y hy hj))

end SubBoundary

/-! ## The substitution principle -/

open SubBoundary in
/-- **Connectivity depends only on the boundary partitions.**  If corresponding parts induce the
same reachability relation on the boundary set `B`, and each part's non-boundary vertices are
private to it, then the two unions have the same reachability relation on `B`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {iota : Type*} [Fintype iota]
    [DecidableEq iota] (S S' : iota → Finset (Sym2 V)) (B : Finset V)
    (hsame : ∀ i, ∀ p ∈ B, ∀ q ∈ B,
      ((ofEdges (S i)).Reachable p q ↔ (ofEdges (S' i)).Reachable p q))
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ B → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    (hsupp' : ∀ i, ∀ e ∈ S' i, ∀ v ∈ e, v ∉ B → ∀ j, j ≠ i → ∀ f ∈ S' j, v ∉ f)
    (x y : V) (hx : x ∈ B) (hy : y ∈ B) :
    ((ofEdges (Finset.univ.biUnion S)).Reachable x y
      ↔ (ofEdges (Finset.univ.biUnion S')).Reachable x y) :=
  ⟨reachable_of_reachable (fun i p hp q hq => (hsame i p hp q hq).1) hsupp hx hy,
   reachable_of_reachable (fun i p hp q hq => (hsame i p hp q hq).2) hsupp' hx hy⟩

#print axioms SubBoundary.exists_edge_of_reachable_ne
#print axioms SubBoundary.reachable_union
#print axioms SubBoundary.adj_union_part
#print axioms SubBoundary.good_step
#print axioms SubBoundary.good_transport
#print axioms SubBoundary.reachable_of_reachable
#print axioms solution
