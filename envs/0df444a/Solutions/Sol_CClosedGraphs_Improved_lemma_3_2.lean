-- Prove2me | solution 1 for CClosedGraphs.Improved.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T00:29:55.533172+00:00
-- url     : https://prove2.me/submissions/a3625a6d-fd42-492d-bbd2-c155364f08e0

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace Prove2SwarmSubmission
open CClosedGraphs.Improved

set_option autoImplicit false

namespace CClosedGraphs.Improved

open Classical
open Finset

variable {V : Type*} [Fintype V]

/-! ## Finite helpers for `A = W ∩ N(v)` and `W ∩ N(v) ∩ N(u)`

These definitions are deliberately computational descriptions of the target's
`Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)` and of the set
`W ∩ G.commonNeighbors v u`.  They are useful when counting subsets. -/

/-- The finite set version of `A = W ∩ N_G(v)`. -/
noncomputable def nbrsInFinset (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)

/-- The finite set version of `W ∩ N_G(v) ∩ N_G(u)`. -/
noncomputable def commonNbrsInFinset (G : SimpleGraph V) (W : Set V) (v u : V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x ∧ G.Adj u x)

@[simp]
theorem mem_nbrsInFinset {G : SimpleGraph V} {W : Set V} {v x : V} :
    x ∈ nbrsInFinset G W v ↔ x ∈ W ∧ G.Adj v x := by
  simp [nbrsInFinset]

@[simp]
theorem mem_commonNbrsInFinset {G : SimpleGraph V} {W : Set V} {v u x : V} :
    x ∈ commonNbrsInFinset G W v u ↔
      x ∈ W ∧ G.Adj v x ∧ G.Adj u x := by
  simp [commonNbrsInFinset]

/-! ## The local c-closure bound -/

omit [Fintype V] in
/-- If `u` is at distance two from `v` inside `W`, then the two vertices have
at most `c - 1` common neighbours inside `W`.

The proof uses only the fact that `u ∈ W`, `u ≠ v`, and `¬ G.Adj v u` from
`u ∈ dist2In G W v`.  The two-edge witness in the definition of `dist2In` is
not needed for this bound. -/
theorem ncard_commonNeighbors_le_pred_of_dist2In
    {c : ℕ} (_hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    (W ∩ G.commonNeighbors v u).ncard ≤ c - 1 := by
  have huW : u ∈ W := hu.1
  have huv : u ≠ v := hu.2.1
  have hnonadj : ¬ G.Adj v u := hu.2.2.1
  have hnot_ge : ¬ c ≤ (W ∩ G.commonNeighbors v u).ncard := by
    intro hge
    exact hnonadj (hW v hv u huW huv.symm hge)
  exact Nat.le_sub_one_of_lt (Nat.lt_of_not_ge hnot_ge)

/-- Finite-cardinality form of the local closure bound, stated for the
explicit finite set `W ∩ N(v) ∩ N(u)`. -/
theorem card_commonNbrsInFinset_le_pred
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    (commonNbrsInFinset G W v u).card ≤ c - 1 := by
  have hset : (commonNbrsInFinset G W v u : Set V) =
      W ∩ G.commonNeighbors v u := by
    ext x
    simp [commonNbrsInFinset, SimpleGraph.commonNeighbors, and_assoc]; tauto
  rw [← Set.ncard_coe_finset]
  rw [hset]
  exact ncard_commonNeighbors_le_pred_of_dist2In hc hW hv hu

/-! ## Characterizing subsets whose common neighbourhood contains `u` -/

/-- For a subset `S ⊆ A = W ∩ N_G(v)`, the vertex `u` is in `N(S)` exactly
when `S` is contained in the finite set `W ∩ N_G(v) ∩ N_G(u)`.

This is the fiber characterization needed for double counting.  The proof of
the forward direction uses adjacency symmetry only because `commonNbrs G S`
records the edge as `(s,u)`, while `G.commonNeighbors v u` records it as
`(u,s)`. -/
theorem mem_commonNbrs_iff_subset_commonNbrsInFinset
    {G : SimpleGraph V} {W : Set V} {v u : V} {S : Finset V}
    (hS : S ⊆ nbrsInFinset G W v) :
    u ∈ commonNbrs G S ↔ S ⊆ commonNbrsInFinset G W v u := by
  constructor
  · intro hu x hx
    have hxA := mem_nbrsInFinset.mp (hS hx)
    exact mem_commonNbrsInFinset.mpr
      ⟨hxA.1, hxA.2, G.adj_symm (hu x hx)⟩
  · intro hsub x hx
    have hx' := mem_commonNbrsInFinset.mp (hsub hx)
    exact G.adj_symm hx'.2.2

/-- The same subset characterization using exactly the set intersection from
the target statement. -/
theorem mem_commonNbrs_iff_subset_commonNeighbors
    {G : SimpleGraph V} {W : Set V} {v u : V} {S : Finset V}
    (hS : S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset) :
    u ∈ commonNbrs G S ↔
      (S : Set V) ⊆ W ∩ G.commonNeighbors v u := by
  have hSsub : S ⊆ nbrsInFinset G W v := by
    simpa [nbrsInFinset] using (Finset.mem_powerset.mp hS)
  rw [mem_commonNbrs_iff_subset_commonNbrsInFinset hSsub]
  constructor
  · intro hsub x hx
    have hx' := mem_commonNbrsInFinset.mp (hsub (by simpa using hx))
    refine ⟨hx'.1, ?_⟩
    simpa [SimpleGraph.commonNeighbors] using hx'.2
  · intro hsub x hx
    have hx' := hsub (by simpa using hx)
    rw [mem_commonNbrsInFinset]
    exact ⟨hx'.1, by simpa [SimpleGraph.commonNeighbors] using hx'.2⟩

/-! ## Per-vertex fiber bound -/

/-- The number of nonempty subsets `S ⊆ A = W ∩ N_G(v)` with `u ∈ N(S)` is at
most `2 ^ (c - 1)`, for every `u ∈ dist2In G W v`.

All such subsets are subsets of `W ∩ N_G(v) ∩ N_G(u)`, a finite set of size
at most `c - 1`; the nonemptiness condition can therefore be discarded in the
upper bound. -/
theorem fiber_card_le_pow
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    ((nbrsInFinset G W v).powerset.filter
        (fun S => S.Nonempty ∧ u ∈ commonNbrs G S)).card
      ≤ 2 ^ (c - 1) := by
  calc
    ((nbrsInFinset G W v).powerset.filter
        (fun S => S.Nonempty ∧ u ∈ commonNbrs G S)).card
        ≤ (commonNbrsInFinset G W v u).powerset.card := by
          apply Finset.card_le_card
          intro S hS
          rw [Finset.mem_filter] at hS
          exact Finset.mem_powerset.mpr
            ((mem_commonNbrs_iff_subset_commonNbrsInFinset
              (Finset.mem_powerset.mp hS.1)).mp hS.2.2)
    _ = 2 ^ (commonNbrsInFinset G W v u).card := by
          rw [Finset.card_powerset]
    _ ≤ 2 ^ (c - 1) := by
          exact Nat.pow_le_pow_right (by norm_num)
            (card_commonNbrsInFinset_le_pred hc hW hv hu)

/-- The per-vertex fiber bound with the exact filtered-power-set expression
appearing in the target theorem. -/
theorem card_filter_commonNbrs_le_pow
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    (((Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty)).filter
        (fun S => u ∈ commonNbrs G S)).card
      ≤ 2 ^ (c - 1) := by
  simpa [nbrsInFinset, Finset.filter_filter, and_assoc] using
    (fiber_card_le_pow hc hW hv hu)

end CClosedGraphs.Improved


set_option autoImplicit false

namespace CClosedGraphs.Improved

open Classical
open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lemma 3.2: the inherited closure property on the subgraph induced by
the neighbourhood of a vertex of `W`. -/
theorem lemma_3_2 {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V}
    (hv : v ∈ W) :
    IsCClosedOn (c - 1) G (W ∩ G.neighborSet v) := by
  intro u hu w hw huw hcard
  have huW : u ∈ W := hu.1
  have hwW : w ∈ W := hw.1
  have hvu : G.Adj v u := hu.2
  have hvw : G.Adj v w := hw.2
  -- `v` itself is a common neighbour in `W` of the pair `u,w`.
  have hvB : v ∈ W ∩ G.commonNeighbors u w := by
    refine ⟨hv, ?_⟩
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨G.adj_symm hvu, G.adj_symm hvw⟩
  -- `v` is not in the smaller neighbourhood environment.
  have hv_not_A : v ∉ W ∩ G.neighborSet v := by
    intro hvA
    have hvv : G.Adj v v := (SimpleGraph.mem_neighborSet G v v).mp hvA.2
    exact G.loopless.irrefl v hvv
  have hv_not_C : v ∉
      (W ∩ G.neighborSet v) ∩ G.commonNeighbors u w := by
    intro hvC
    exact hv_not_A hvC.1
  -- Adding the new vertex `v` increases the common-neighbour count by one.
  have hCsubB :
      ((W ∩ G.neighborSet v) ∩ G.commonNeighbors u w) ⊆
        W ∩ G.commonNeighbors u w := by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hsub :
      (((W ∩ G.neighborSet v) ∩ G.commonNeighbors u w) ∪ {v}) ⊆
        W ∩ G.commonNeighbors u w := by
    intro x hx
    rcases hx with hxC | hxv
    · exact hCsubB hxC
    · rw [Set.mem_singleton_iff] at hxv
      subst x
      exact hvB
  have hdisj :
      Disjoint ((W ∩ G.neighborSet v) ∩ G.commonNeighbors u w) {v} := by
    rw [Set.disjoint_singleton_right]
    exact hv_not_C
  have hunion :
      ((((W ∩ G.neighborSet v) ∩ G.commonNeighbors u w) ∪ {v}).ncard) =
        (((W ∩ G.neighborSet v) ∩ G.commonNeighbors u w).ncard + 1) := by
    rw [Set.ncard_union_eq hdisj]
    simp
  have hcB : c ≤ (W ∩ G.commonNeighbors u w).ncard := by
    calc
      c = (c - 1) + 1 := (Nat.sub_add_cancel hc).symm
      _ ≤ ((W ∩ G.neighborSet v) ∩ G.commonNeighbors u w).ncard + 1 :=
        Nat.add_le_add_right hcard 1
      _ = (((W ∩ G.neighborSet v) ∩ G.commonNeighbors u w) ∪ {v}).ncard :=
        hunion.symm
      _ ≤ (W ∩ G.commonNeighbors u w).ncard := Set.ncard_le_ncard hsub
  exact hW u huW w hwW huw hcB

end CClosedGraphs.Improved

end Prove2SwarmSubmission

open CClosedGraphs.Improved
open Classical

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W) :
    IsCClosedOn (c - 1) G (W ∩ G.neighborSet v) := by
  exact Prove2SwarmSubmission.CClosedGraphs.Improved.lemma_3_2 hc hW hv
