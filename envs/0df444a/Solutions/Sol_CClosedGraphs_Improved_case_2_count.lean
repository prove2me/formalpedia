-- Prove2me | solution 1 for CClosedGraphs.Improved.case_2_count
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T05:25:34.540996+00:00
-- url     : https://prove2.me/submissions/1e264185-17c2-4512-b4c2-7fc509775385

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

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {W : Set V} {v : V}

set_option linter.unusedSectionVars false

omit [DecidableEq V] in
/-- Membership normal form for the maximal-clique finset. -/
lemma mem_maxCliquesIn_iff {K : Finset V} :
    K ∈ CClosedGraphs.Peeling.maxCliquesIn G W ↔
      (↑K : Set V) ⊆ W ∧ G.IsClique (↑K : Set V) ∧
      ∀ ⦃T : Finset V⦄, (↑T : Set V) ⊆ W →
        G.IsClique (↑T : Set V) → K ⊆ T → T ⊆ K := by
  classical
  rw [CClosedGraphs.Peeling.maxCliquesIn]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [Maximal]
  constructor
  · rintro ⟨⟨hKW, hKclique⟩, hKmax⟩
    exact ⟨hKW, hKclique, fun T hTW hTclique hKT => hKmax ⟨hTW, hTclique⟩ hKT⟩
  · rintro ⟨hKW, hKclique, hKmax⟩
    exact ⟨⟨hKW, hKclique⟩, fun T hT hKT => hKmax hT.1 hT.2 hKT⟩

/-- Erasing the distinguished vertex sends a left maximal clique to a right one. -/
lemma erase_mem_maxCliquesIn_neighborSet
    {K : Finset V}
    (hK : K ∈ (CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K)) :
    K.erase v ∈ CClosedGraphs.Peeling.maxCliquesIn G (W ∩ G.neighborSet v) := by
  classical
  have hKmem : K ∈ CClosedGraphs.Peeling.maxCliquesIn G W :=
    (Finset.mem_filter.mp hK).1
  have hvK : v ∈ K := (Finset.mem_filter.mp hK).2
  rw [mem_maxCliquesIn_iff] at hKmem ⊢
  rcases hKmem with ⟨hKW, hKclique, hKmax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_erase] at hx
    have hxK : x ∈ K := hx.2
    have hxW : x ∈ W := hKW (by exact_mod_cast hxK)
    have hxN : x ∈ G.neighborSet v := by
      rw [SimpleGraph.mem_neighborSet]
      exact G.adj_symm (hKclique hxK hvK hx.1)
    exact ⟨hxW, hxN⟩
  · exact hKclique.subset (by
      intro x hx
      exact (Finset.mem_erase.mp hx).2)
  · intro T hTdom hTclique hKeraseT
    let U : Finset V := insert v T
    have hUdom : (↑U : Set V) ⊆ W := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hxT
      · exact hKW hvK
      · exact (hTdom (by exact_mod_cast hxT)).1
    have hUclique : G.IsClique (↑U : Set V) := by
      dsimp [U]
      rw [Finset.coe_insert]
      exact hTclique.insert (fun x hx hne =>
        ((SimpleGraph.mem_neighborSet G v x).mp ((hTdom (by exact_mod_cast hx)).2)))
    have hKsubU : K ⊆ U := by
      intro x hxK
      by_cases hxv : x = v
      · rw [Finset.mem_insert]
        exact Or.inl hxv
      · rw [Finset.mem_insert]
        right
        exact hKeraseT (by
          rw [Finset.mem_erase]
          exact ⟨hxv, hxK⟩)
    have hUsubK : U ⊆ K := hKmax hUdom hUclique hKsubU
    intro x hxT
    rw [Finset.mem_erase]
    refine ⟨?_, hUsubK ?_⟩
    · have hxN : x ∈ G.neighborSet v := (hTdom (by exact_mod_cast hxT)).2
      exact (G.ne_of_adj (((SimpleGraph.mem_neighborSet G v x).mp hxN))).symm
    · rw [Finset.mem_insert]
      exact Or.inr hxT

/-- Inserting the distinguished vertex sends a right maximal clique to a left one. -/
lemma insert_mem_maxCliquesIn_of_mem_neighborSet
    {L : Finset V}
    (hL : L ∈ CClosedGraphs.Peeling.maxCliquesIn G (W ∩ G.neighborSet v))
    (hvW : v ∈ W) :
    insert v L ∈ CClosedGraphs.Peeling.maxCliquesIn G W := by
  classical
  rw [mem_maxCliquesIn_iff] at hL ⊢
  rcases hL with ⟨hLdom, hLclique, hLmax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hxL
    · exact hvW
    · exact (hLdom (by exact_mod_cast hxL)).1
  · rw [Finset.coe_insert]
    exact hLclique.insert (fun x hx hne =>
      ((SimpleGraph.mem_neighborSet G v x).mp ((hLdom (by exact_mod_cast hx)).2)))
  · intro T hTW hTclique hInsLT
    have hvT : v ∈ T := hInsLT (by rw [Finset.mem_insert]; exact Or.inl rfl)
    have hEraseDom : (↑(T.erase v) : Set V) ⊆ W ∩ G.neighborSet v := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_erase] at hx
      refine ⟨hTW (by exact_mod_cast hx.2), ?_⟩
      rw [SimpleGraph.mem_neighborSet]
      exact hTclique hvT hx.2 hx.1.symm
    have hEraseClique : G.IsClique (↑(T.erase v) : Set V) :=
      hTclique.subset (by
        intro x hx
        exact (Finset.mem_erase.mp hx).2)
    have hLsubErase : L ⊆ T.erase v := by
      intro x hxL
      rw [Finset.mem_erase]
      refine ⟨?_, hInsLT ?_⟩
      · have hxN : x ∈ G.neighborSet v := (hLdom (by exact_mod_cast hxL)).2
        exact (G.ne_of_adj (((SimpleGraph.mem_neighborSet G v x).mp hxN))).symm
      · rw [Finset.mem_insert]
        exact Or.inr hxL
    have hEraseSubL : T.erase v ⊆ L := hLmax hEraseDom hEraseClique hLsubErase
    intro x hxT
    by_cases hxv : x = v
    · rw [Finset.mem_insert]
      exact Or.inl hxv
    · rw [Finset.mem_insert]
      right
      exact hEraseSubL (by
        rw [Finset.mem_erase]
        exact ⟨hxv, hxT⟩)

/-- The target identity: maximal cliques through `v` correspond to maximal cliques in the
neighbourhood of `v` by deleting/inserting `v`, including the isolated-vertex case. -/
theorem card_maxCliques_mem_eq
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K)).card =
      CClosedGraphs.Peeling.numMaxCliquesIn G (W ∩ G.neighborSet v) := by
  classical
  rw [CClosedGraphs.Peeling.numMaxCliquesIn]
  refine Finset.card_bij'
    (fun K _ => K.erase v) (fun L _ => insert v L) ?_ ?_ ?_ ?_
  · intro K hK
    exact erase_mem_maxCliquesIn_neighborSet hK
  · intro L hL
    exact Finset.mem_filter.mpr
      ⟨insert_mem_maxCliquesIn_of_mem_neighborSet hL hv, by simp⟩
  · intro K hK
    exact Finset.insert_erase (Finset.mem_filter.mp hK).2
  · intro L hL
    have hLdom : (↑L : Set V) ⊆ W ∩ G.neighborSet v :=
      (mem_maxCliquesIn_iff.mp hL).1
    have hvL : v ∉ L := by
      intro hvIn
      have hmem : v ∈ W ∩ G.neighborSet v := hLdom (by exact_mod_cast hvIn)
      exact G.irrefl ((SimpleGraph.mem_neighborSet G v v).mp hmem.2)
    exact Finset.erase_insert hvL

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

/-- The exact neighbor finset `W ∩ N_G(v)` used by the target sum. -/
noncomputable abbrev nbrsIn (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)

/-- The source fiber index `S = K ∩ N_G(v)`. -/
noncomputable abbrev sourceIndex (K : Finset V) (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  K ∩ nbrsIn G W v

/-- The restricted vertex set `N(S) ∩ N₂(v)` from the target sum. -/
noncomputable abbrev fiberDomain (G : SimpleGraph V) (W : Set V) (v : V) (S : Finset V) : Set V :=
  commonNbrs G S ∩ dist2In G W v

/-- Finite-set form of the fiber domain, used for intersections with ambient finsets. -/
noncomputable abbrev fiberFinset (G : SimpleGraph V) (W : Set V) (v : V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ commonNbrs G S ∧ x ∈ dist2In G W v)

omit [DecidableEq V] in
@[simp] lemma mem_fiberFinset {S : Finset V} {x : V} :
    x ∈ fiberFinset G W v S ↔ x ∈ commonNbrs G S ∧ x ∈ dist2In G W v := by
  simp [fiberFinset]

omit [DecidableEq V] in
lemma coe_fiberFinset (S : Finset V) :
    (↑(fiberFinset G W v S) : Set V) = fiberDomain G W v S := by
  ext x
  simp [fiberFinset, fiberDomain]

/-- The source vertex `y` witnessing that `S` is nonempty also lies in `W ∩ N(v)`. -/
lemma sourceIndex_nonempty
    {K : Finset V}
    (hK : K ∈ CClosedGraphs.Peeling.maxCliquesIn G W)
    (hP : v ∉ K ∧ ∃ y ∈ K, G.Adj v y) :
    (sourceIndex K G W v).Nonempty := by
  rcases hP with ⟨_hvK, y, hyK, hvy⟩
  have hKW : (↑K : Set V) ⊆ W := (mem_maxCliquesIn_iff.mp hK).1
  have hyW : y ∈ W := hKW (by exact_mod_cast hyK)
  exact ⟨y, by simp [sourceIndex, nbrsIn, hyK, hyW, hvy]⟩

/-- The source index is a nonempty member of the powerset of `W ∩ N(v)`. -/
lemma sourceIndex_mem
    {K : Finset V}
    (hK : K ∈ CClosedGraphs.Peeling.maxCliquesIn G W)
    (hP : v ∉ K ∧ ∃ y ∈ K, G.Adj v y) :
    sourceIndex K G W v ∈
      (nbrsIn G W v).powerset.filter (fun S => Finset.Nonempty S) := by
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.inter_subset_right, sourceIndex_nonempty hK hP⟩

/-- Every vertex of a source clique is either in `S = K ∩ N(v)` or lies in the
fiber domain `N(S) ∩ N₂(v)`. -/
lemma source_subset_index_union_fiber
    {K : Finset V}
    (hK : K ∈ CClosedGraphs.Peeling.maxCliquesIn G W)
    (hP : v ∉ K ∧ ∃ y ∈ K, G.Adj v y) :
    K ⊆ sourceIndex K G W v ∪
      (K ∩ fiberFinset G W v (sourceIndex K G W v)) := by
  rcases hP with ⟨hvK, y, hyK, hvy⟩
  rcases mem_maxCliquesIn_iff.mp hK with ⟨hKW, hKclique, _hKmax⟩
  intro x hxK
  by_cases hxA : x ∈ nbrsIn G W v
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxK, hxA⟩))
  · have hxW : x ∈ W := hKW (by exact_mod_cast hxK)
    have hxne_v : x ≠ v := by
      intro hxv
      subst x
      exact hvK hxK
    have hnonadj : ¬ G.Adj v x := by
      intro hvx
      exact hxA (by simp [nbrsIn, hxW, hvx])
    have hyW : y ∈ W := hKW (by exact_mod_cast hyK)
    have hyA : y ∈ nbrsIn G W v := by simp [nbrsIn, hyW, hvy]
    have hy_ne_x : y ≠ x := by
      intro hyx
      subst y
      exact hxA hyA
    have hxCommon : x ∈ commonNbrs G (sourceIndex K G W v) := by
      intro s hs
      have hsK : s ∈ K := (Finset.mem_inter.mp hs).1
      have hs_ne_x : s ≠ x := by
        intro hsx
        subst s
        exact hxA (Finset.mem_inter.mp hs).2
      exact hKclique (by exact_mod_cast hsK) (by exact_mod_cast hxK) hs_ne_x
    have hxDist2 : x ∈ dist2In G W v := by
      refine ⟨hxW, hxne_v, hnonadj, y, hyW, hvy, ?_⟩
      exact hKclique (by exact_mod_cast hyK) (by exact_mod_cast hxK) hy_ne_x
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_inter.mpr ⟨hxK, by simp [fiberFinset, hxCommon, hxDist2]⟩))

/-- Key decomposition: the restriction `K ∩ (N(S) ∩ N₂(v))` of a source clique is a
maximal clique in the induced graph on the fiber domain. -/
lemma source_restricted_mem_maxCliquesIn
    {K : Finset V}
    (hK : K ∈ CClosedGraphs.Peeling.maxCliquesIn G W)
    (hP : v ∉ K ∧ ∃ y ∈ K, G.Adj v y) :
    K ∩ fiberFinset G W v (sourceIndex K G W v) ∈
      CClosedGraphs.Peeling.maxCliquesIn G (fiberDomain G W v (sourceIndex K G W v)) := by
  let S : Finset V := sourceIndex K G W v
  let C : Set V := fiberDomain G W v S
  let Cfin : Finset V := fiberFinset G W v S
  have hSnonempty : S.Nonempty := sourceIndex_nonempty hK hP
  rcases mem_maxCliquesIn_iff.mp hK with ⟨hKW, hKclique, hKmax⟩
  have hSsubK : S ⊆ K := Finset.inter_subset_left
  have hSclique : G.IsClique (↑S : Set V) :=
    hKclique.subset (by intro x hx; exact hSsubK (by exact_mod_cast hx))
  have hCW : C ⊆ W := by
    intro x hx
    exact (Set.mem_of_mem_inter_right hx).1
  have hCCommon : C ⊆ commonNbrs G S := by
    intro x hx
    exact Set.mem_of_mem_inter_left hx
  have hLclique : G.IsClique (↑(K ∩ Cfin) : Set V) :=
    hKclique.subset (by
      intro x hx
      exact (Finset.mem_inter.mp (by exact_mod_cast hx)).1)
  have hLmax : ∀ ⦃T : Finset V⦄, (↑T : Set V) ⊆ C →
      G.IsClique (↑T : Set V) → K ∩ Cfin ⊆ T → T ⊆ K ∩ Cfin := by
    intro T hTC hTclique hLT
    have hTC' : (↑T : Set V) ⊆ fiberDomain G W v S := hTC
    let U : Finset V := S ∪ T
    have hUW : (↑U : Set V) ⊆ W := by
      intro x hxU
      have hxU' : x ∈ S ∪ T := by exact_mod_cast hxU
      rcases Finset.mem_union.mp hxU' with hxS | hxT
      · exact hKW (by exact_mod_cast hSsubK hxS)
      · exact hCW (hTC' (by exact_mod_cast hxT))
    have hUclique : G.IsClique (↑U : Set V) := by
      intro a ha b hb hne
      have ha' : a ∈ S ∪ T := by exact_mod_cast ha
      have hb' : b ∈ S ∪ T := by exact_mod_cast hb
      rcases Finset.mem_union.mp ha' with haS | haT <;>
        rcases Finset.mem_union.mp hb' with hbS | hbT
      · exact hSclique (by exact_mod_cast haS) (by exact_mod_cast hbS) hne
      · have hbCommon : b ∈ commonNbrs G S := hCCommon (hTC' (by exact_mod_cast hbT))
        exact hbCommon a haS
      · have haCommon : a ∈ commonNbrs G S := hCCommon (hTC' (by exact_mod_cast haT))
        exact G.adj_symm (haCommon b hbS)
      · exact hTclique (by exact_mod_cast haT) (by exact_mod_cast hbT) hne
    have hKsubU : K ⊆ U := by
      intro x hxK
      rcases Finset.mem_union.mp (source_subset_index_union_fiber hK hP hxK) with hxS | hxL
      · exact Finset.mem_union.mpr (Or.inl hxS)
      · exact Finset.mem_union.mpr (Or.inr (hLT hxL))
    have hUsubK : U ⊆ K := hKmax hUW hUclique hKsubU
    intro x hxT
    refine Finset.mem_inter.mpr ⟨hUsubK (Finset.mem_union.mpr (Or.inr hxT)), ?_⟩
    change x ∈ fiberFinset G W v S
    rw [mem_fiberFinset]
    exact hTC' (by exact_mod_cast hxT)
  have hmem : K ∩ Cfin ∈ CClosedGraphs.Peeling.maxCliquesIn G C := by
    refine mem_maxCliquesIn_iff.mpr ⟨?_, hLclique, hLmax⟩
    rw [Finset.coe_inter, coe_fiberFinset]
    exact Set.inter_subset_right
  simpa [S, C, Cfin] using hmem

/-- A source clique is recovered from its index and its restricted fiber clique. -/
lemma source_eq_index_union_restricted
    {K : Finset V}
    (hK : K ∈ CClosedGraphs.Peeling.maxCliquesIn G W)
    (hP : v ∉ K ∧ ∃ y ∈ K, G.Adj v y) :
    sourceIndex K G W v ∪
      (K ∩ fiberFinset G W v (sourceIndex K G W v)) = K := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxL
    · exact (Finset.mem_inter.mp hxS).1
    · exact (Finset.mem_inter.mp hxL).1
  · exact source_subset_index_union_fiber hK hP

/-- The exact fiberwise injection from the filtered source maximal cliques to the
dependent disjoint union indexed by nonempty subsets of `W ∩ N(v)`. -/
theorem card_source_le_sigma
    (G : SimpleGraph V) (W : Set V) {v : V} (_hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card ≤
      (((nbrsIn G W v).powerset.filter (fun S => Finset.Nonempty S)).sigma
        (fun S => CClosedGraphs.Peeling.maxCliquesIn G (fiberDomain G W v S))).card := by
  classical
  let lhs := (CClosedGraphs.Peeling.maxCliquesIn G W).filter
    (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)
  let idx := (nbrsIn G W v).powerset.filter (fun S => Finset.Nonempty S)
  let target := idx.sigma
    (fun S => CClosedGraphs.Peeling.maxCliquesIn G (fiberDomain G W v S))
  let f : Finset V → (S : Finset V) × Finset V :=
    fun K => ⟨sourceIndex K G W v,
      K ∩ fiberFinset G W v (sourceIndex K G W v)⟩
  have hmaps : Set.MapsTo f (↑lhs : Set (Finset V)) (↑target : Set ((S : Finset V) × Finset V)) := by
    intro K hK
    have hK' : K ∈ (CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y) := by simpa [lhs] using hK
    rcases Finset.mem_filter.mp hK' with ⟨hKmem, hP⟩
    have hS : sourceIndex K G W v ∈ idx := by
      simpa [idx] using sourceIndex_mem hKmem hP
    have hL : K ∩ fiberFinset G W v (sourceIndex K G W v) ∈
        CClosedGraphs.Peeling.maxCliquesIn G (fiberDomain G W v (sourceIndex K G W v)) :=
      source_restricted_mem_maxCliquesIn hKmem hP
    have : f K ∈ target := by
      rw [Finset.mem_sigma]
      exact ⟨by simpa [f] using hS, by simpa [f] using hL⟩
    simpa using this
  have hinj : Set.InjOn f (↑lhs : Set (Finset V)) := by
    intro K hK K' hK' hEq
    have hK'filter : K ∈ (CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y) := by simpa [lhs] using hK
    have hK''filter : K' ∈ (CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y) := by simpa [lhs] using hK'
    rcases Finset.mem_filter.mp hK'filter with ⟨hKmem, hP⟩
    rcases Finset.mem_filter.mp hK''filter with ⟨hK'mem, hP'⟩
    have hS : sourceIndex K G W v = sourceIndex K' G W v := by
      simpa [f] using congrArg Sigma.fst hEq
    have hL : K ∩ fiberFinset G W v (sourceIndex K G W v) =
        K' ∩ fiberFinset G W v (sourceIndex K' G W v) := by
      simpa [f] using congrArg Sigma.snd hEq
    have hL' : K ∩ fiberFinset G W v (sourceIndex K' G W v) =
        K' ∩ fiberFinset G W v (sourceIndex K' G W v) := by
      simpa [hS] using hL
    calc
      K = sourceIndex K G W v ∪
          (K ∩ fiberFinset G W v (sourceIndex K G W v)) :=
        (source_eq_index_union_restricted hKmem hP).symm
      _ = sourceIndex K' G W v ∪
          (K' ∩ fiberFinset G W v (sourceIndex K' G W v)) := by rw [hS, hL']
      _ = K' := source_eq_index_union_restricted hK'mem hP'
  exact Finset.card_le_card_of_injOn f hmaps hinj

/-- The frozen inequality (2), with the exact nonempty-powerset sum. -/
theorem ineq_2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card ≤
      ∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => Finset.Nonempty S),
        CClosedGraphs.Peeling.numMaxCliquesIn G (commonNbrs G S ∩ dist2In G W v) := by
  classical
  have h := card_source_le_sigma G W hv
  rw [Finset.card_sigma] at h
  simpa [nbrsIn, fiberDomain, CClosedGraphs.Peeling.numMaxCliquesIn] using h


noncomputable def dist2InFinset (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => u ∈ dist2In G W v)

@[simp]
theorem mem_dist2InFinset {G : SimpleGraph V} {W : Set V} {v u : V} :
    u ∈ dist2InFinset G W v ↔ u ∈ dist2In G W v := by
  simp [dist2InFinset]

/-- The finite set of neighbours of `v` inside `W`. -/
noncomputable def nbrsInFinset' (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  Finset.univ.filter (fun y => y ∈ W ∧ G.Adj v y)

@[simp]
theorem mem_nbrsInFinset' {G : SimpleGraph V} {W : Set V} {v y : V} :
    y ∈ nbrsInFinset' G W v ↔ y ∈ W ∧ G.Adj v y := by
  simp [nbrsInFinset']

/-- Fiber of candidates at a first-step vertex `y`: vertices of `W` adjacent to `y`. -/
noncomputable def neighborFiberInFinset (G : SimpleGraph V) (W : Set V) (y : V) : Finset V :=
  Finset.univ.filter (fun u => u ∈ W ∧ G.Adj y u)

@[simp]
theorem mem_neighborFiberInFinset {G : SimpleGraph V} {W : Set V} {y u : V} :
    u ∈ neighborFiberInFinset G W y ↔ u ∈ W ∧ G.Adj y u := by
  simp [neighborFiberInFinset]

/-- The target's second-distance set in `W` is contained in the union, over
first-step vertices `y ∈ A = W ∩ N(v)`, of the within-`W` neighbourhood of `y`. -/
theorem dist2InFinset_subset_biUnion_neighborFiber
    {G : SimpleGraph V} {W : Set V} {v : V} :
    dist2InFinset G W v ⊆
      (nbrsInFinset' G W v).biUnion (neighborFiberInFinset G W) := by
  intro u hu
  rw [mem_dist2InFinset] at hu
  obtain ⟨huW, huv, hnonadj, y, hyW, hvy, hyu⟩ := hu
  refine Finset.mem_biUnion.mpr ⟨y, ?_, ?_⟩
  · rw [mem_nbrsInFinset']
    exact ⟨hyW, hvy⟩
  · rw [mem_neighborFiberInFinset]
    exact ⟨huW, hyu⟩

/-- Every fiber at `y ∈ A` is exactly `W ∩ N(y)`, so its cardinality is
bounded by `Δ` under the target's within-`W` degree hypothesis. -/
theorem neighborFiberInFinset_card_le
    {G : SimpleGraph V} {W : Set V} {y : V} (hyW : y ∈ W) {Δ : ℕ}
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (neighborFiberInFinset G W y).card ≤ Δ := by
  rw [← Set.ncard_coe_finset]
  convert hΔ y hyW using 2
  ext u
  simp [neighborFiberInFinset, SimpleGraph.mem_neighborSet]

/-- `|A| ≤ Δ`, where `A = W ∩ N(v)`. -/
theorem nbrsInFinset'_card_le
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W) {Δ : ℕ}
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (nbrsInFinset' G W v).card ≤ Δ := by
  rw [← Set.ncard_coe_finset]
  convert hΔ v hv using 2
  ext u
  simp [nbrsInFinset', SimpleGraph.mem_neighborSet]


/-- Incidence count for a single subset: cardinality of a common-neighbour
intersection with the internal distance-two set is the sum of its indicator
over the finite set `B`. -/
theorem ncard_inter_dist2In_eq_sum_indicator (G : SimpleGraph V) (W : Set V) (v : V)
    (C : Set V) :
    (C ∩ dist2In G W v).ncard =
      ∑ u ∈ dist2InFinset G W v, if u ∈ C then 1 else 0 := by
  let B : Finset V := dist2InFinset G W v
  have hset : C ∩ dist2In G W v = (B.filter (fun u => u ∈ C) : Set V) := by
    ext u
    simp [B, and_comm]
  rw [hset, Set.ncard_coe_finset]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- First conclusion of the target, with its exact finite sum. -/
theorem sum_commonNbrs_dist2In_le
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W) :
    (∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) ≤
      (dist2In G W v).ncard * 2 ^ (c - 1) := by
  let A : Finset V := Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)
  let B : Finset V := dist2InFinset G W v
  let s : Finset (Finset V) := A.powerset.filter (fun S => S.Nonempty)
  have hBcard : (dist2In G W v).ncard = B.card := by
    rw [← Set.ncard_coe_finset B]
    congr 1
    ext u
    simp [B]
  have hstep : (∑ S ∈ s, (commonNbrs G S ∩ dist2In G W v).ncard) =
      ∑ u ∈ B, ∑ S ∈ s, if u ∈ commonNbrs G S then 1 else 0 := by
    calc
      (∑ S ∈ s, (commonNbrs G S ∩ dist2In G W v).ncard)
          = ∑ S ∈ s, ∑ u ∈ B, if u ∈ commonNbrs G S then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro S hS
              simpa [B] using
                (ncard_inter_dist2In_eq_sum_indicator G W v (commonNbrs G S))
      _ = ∑ u ∈ B, ∑ S ∈ s, if u ∈ commonNbrs G S then 1 else 0 := by
              rw [Finset.sum_comm]
  rw [show (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)) = A by rfl]
  rw [show (∑ S ∈ A.powerset.filter (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) =
      ∑ S ∈ s, (commonNbrs G S ∩ dist2In G W v).ncard by rfl]
  rw [hstep]
  calc
    (∑ u ∈ B, ∑ S ∈ s, if u ∈ commonNbrs G S then 1 else 0)
        = ∑ u ∈ B, ((s.filter (fun S => u ∈ commonNbrs G S)).card : ℕ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.sum_boole]
            rfl
    _ ≤ ∑ u ∈ B, 2 ^ (c - 1) := by
            apply Finset.sum_le_sum
            intro u hu
            have huB : u ∈ dist2In G W v := by simpa [B] using hu
            simpa [A, s] using card_filter_commonNbrs_le_pow hc hW hv huB
    _ = B.card * 2 ^ (c - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rfl
    _ = (dist2In G W v).ncard * 2 ^ (c - 1) := by rw [hBcard]

/-- Distance-two degree bound: the internal second neighbourhood of `v` has
at most `Δ ^ 2` vertices. This uses exactly the target's within-`W` degree
bound and no c-closure or positivity hypothesis. -/
theorem dist2In_ncard_le_sq
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W) (Δ : ℕ)
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (dist2In G W v).ncard ≤ Δ ^ 2 := by
  let A : Finset V := nbrsInFinset' G W v
  let B : Finset V := dist2InFinset G W v
  have hBcard : (dist2In G W v).ncard = B.card := by
    rw [← Set.ncard_coe_finset B]
    congr 1
    ext u
    simp [B]
  rw [hBcard]
  have hcover : B ⊆ A.biUnion (neighborFiberInFinset G W) := by
    simpa [A, B] using dist2InFinset_subset_biUnion_neighborFiber (G := G) (W := W) (v := v)
  have hfiber : ∀ y ∈ A, (neighborFiberInFinset G W y).card ≤ Δ := by
    intro y hy
    exact neighborFiberInFinset_card_le (mem_nbrsInFinset'.mp hy).1 hΔ
  calc
    B.card ≤ (A.biUnion (neighborFiberInFinset G W)).card := Finset.card_le_card hcover
    _ ≤ A.card * Δ := Finset.card_biUnion_le_card_mul A (neighborFiberInFinset G W) Δ hfiber
    _ ≤ Δ * Δ := Nat.mul_le_mul_right Δ (nbrsInFinset'_card_le hv hΔ)
    _ = Δ ^ 2 := by rw [pow_two]

/-- The same internal second neighbourhood has at most `|W|` vertices. -/
theorem dist2In_ncard_le_ncard
    {G : SimpleGraph V} {W : Set V} {v : V} :
    (dist2In G W v).ncard ≤ W.ncard := by
  exact Set.ncard_le_ncard (fun u hu => hu.1)

/-- The second conclusion of the target, including the `min`. -/
theorem dist2In_ncard_le_min
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W) (Δ : ℕ)
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (dist2In G W v).ncard ≤ min (Δ ^ 2) W.ncard := by
  exact le_min (dist2In_ncard_le_sq hv Δ hΔ) dist2In_ncard_le_ncard


/-- Boundary check at `c = 1`: every per-vertex incidence fiber has the full
empty powerset as its only possible source, hence cardinality at most `1`. -/
theorem fiber_card_le_one_of_c_eq_one
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn 1 G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    ((nbrsInFinset G W v).powerset.filter
        (fun S => S.Nonempty ∧ u ∈ commonNbrs G S)).card ≤ 1 := by
  simpa using (fiber_card_le_pow (c := 1) (by norm_num) hW hv hu)

/-- Boundary check at `Δ = 0`: the distance-two set is empty. -/
theorem dist2In_eq_empty_of_degree_bound_zero
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W)
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ 0) :
    dist2In G W v = ∅ := by
  have hle : (dist2In G W v).ncard ≤ 0 := by
    simpa using dist2In_ncard_le_sq (G := G) (W := W) (v := v) hv 0 hΔ
  exact (Set.ncard_eq_zero (s := dist2In G W v)).mp (Nat.eq_zero_of_le_zero hle)

/-- The frozen target statement, assembled from the independently checked seed
and the two bounds proved in this file. -/
theorem ineq_3 {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) ≤ (dist2In G W v).ncard * 2 ^ (c - 1) ∧
      (dist2In G W v).ncard ≤ min (Δ ^ 2) W.ncard := by
  exact ⟨sum_commonNbrs_dist2In_le hc hW hv,
    dist2In_ncard_le_min hv Δ hΔ⟩


/-- Heredity of the local `c`-closure property under passage to a subset. -/
theorem isCClosedOn_mono {c : ℕ} {G : SimpleGraph V} {W W' : Set V}
    (hW : IsCClosedOn c G W) (hW' : W' ⊆ W) :
    IsCClosedOn c G W' := by
  intro u hu w hw huw hcard
  exact hW u (hW' hu) w (hW' hw) huw
    (le_trans hcard (Set.ncard_le_ncard (by
      intro x hx
      exact ⟨hW' hx.1, hx.2⟩)))

/-- A fibre domain lies in the within-`W` neighbourhood of every vertex of its index. -/
theorem fiberDomain_subset_inter_neighborSet {S : Finset V} {u : V} (hu : u ∈ S) :
    fiberDomain G W v S ⊆ W ∩ G.neighborSet u := by
  intro x hx
  refine ⟨hx.2.1, ?_⟩
  rw [SimpleGraph.mem_neighborSet]
  exact hx.1 u hu

/-- Every fibre domain has at most `Δ` vertices.  This is where the target's
pointwise within-`W` degree bound is used on a vertex of the index. -/
theorem fiberDomain_ncard_le {Δ : ℕ}
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ)
    {S : Finset V} (hS : S ⊆ nbrsIn G W v) {u : V} (hu : u ∈ S) :
    (fiberDomain G W v S).ncard ≤ Δ := by
  have huW : u ∈ W :=
    (mem_nbrsInFinset.mp (by simpa [nbrsIn] using hS hu)).1
  have hsub := fiberDomain_subset_inter_neighborSet (G := G) (W := W) (v := v) hu
  exact le_trans (Set.ncard_le_ncard hsub) (hΔ u huW)

/-- The graph-side fact that makes the nonempty-fibre reindexing possible:
a source clique avoiding `v` must meet `N(S) ∩ N₂(v)` at its index `S`. -/
lemma source_fiber_nonempty {K : Finset V} (hv : v ∈ W)
    (hK : K ∈ CClosedGraphs.Peeling.maxCliquesIn G W)
    (hP : v ∉ K ∧ ∃ y ∈ K, G.Adj v y) :
    (K ∩ fiberFinset G W v (sourceIndex K G W v)).Nonempty := by
  classical
  by_contra hne
  have hKsubS : K ⊆ sourceIndex K G W v := by
    intro x hxK
    rcases Finset.mem_union.mp (source_subset_index_union_fiber hK hP hxK) with hxS | hxL
    · exact hxS
    · exact False.elim (hne ⟨x, hxL⟩)
  have hKsubN : (↑K : Set V) ⊆ G.neighborSet v := by
    intro x hxK
    have hxS : x ∈ sourceIndex K G W v := hKsubS (by exact_mod_cast hxK)
    have hxN : x ∈ nbrsIn G W v := (Finset.mem_inter.mp hxS).2
    exact (mem_nbrsInFinset.mp (by simpa [nbrsIn] using hxN)).2
  rcases mem_maxCliquesIn_iff.mp hK with ⟨hKW, hKclique, hKmax⟩
  have hInsW : (↑(insert v K) : Set V) ⊆ W := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hxK
    · exact hv
    · exact hKW (by exact_mod_cast hxK)
  have hInsClique : G.IsClique (↑(insert v K) : Set V) := by
    rw [Finset.coe_insert]
    exact hKclique.insert (fun x hx _hne => hKsubN (by exact_mod_cast hx))
  have hsub : insert v K ⊆ K := hKmax hInsW hInsClique (Finset.subset_insert v K)
  exact hP.1 (hsub (Finset.mem_insert_self v K))

/-- The re-indexed injection: only nonempty fibres occur, and each avoiding-`v`
maximal clique contributes a maximal clique in its own fibre domain. -/
theorem card_source_le_sigma_nonempty
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card ≤
      (((nbrsIn G W v).powerset.filter
          (fun S => Finset.Nonempty S ∧ (fiberFinset G W v S).Nonempty)).sigma
        (fun S => CClosedGraphs.Peeling.maxCliquesIn G (fiberDomain G W v S))).card := by
  classical
  let lhs := (CClosedGraphs.Peeling.maxCliquesIn G W).filter
    (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)
  let idx := (nbrsIn G W v).powerset.filter
    (fun S => Finset.Nonempty S ∧ (fiberFinset G W v S).Nonempty)
  let target := idx.sigma
    (fun S => CClosedGraphs.Peeling.maxCliquesIn G (fiberDomain G W v S))
  let f : Finset V → (S : Finset V) × Finset V :=
    fun K => ⟨sourceIndex K G W v,
      K ∩ fiberFinset G W v (sourceIndex K G W v)⟩
  have hmaps : Set.MapsTo f (↑lhs : Set (Finset V)) (↑target : Set ((S : Finset V) × Finset V)) := by
    intro K hK
    have hK' : K ∈ (CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y) := by simpa [lhs] using hK
    rcases Finset.mem_filter.mp hK' with ⟨hKmem, hP⟩
    have hSbase : sourceIndex K G W v ∈
        (nbrsIn G W v).powerset.filter (fun S => Finset.Nonempty S) :=
      sourceIndex_mem hKmem hP
    have hX : (fiberFinset G W v (sourceIndex K G W v)).Nonempty := by
      rcases source_fiber_nonempty hv hKmem hP with ⟨x, hx⟩
      exact ⟨x, (Finset.mem_inter.mp hx).2⟩
    have hS : sourceIndex K G W v ∈ idx := by
      rw [Finset.mem_filter] at hSbase ⊢
      exact ⟨hSbase.1, hSbase.2, hX⟩
    have hL : K ∩ fiberFinset G W v (sourceIndex K G W v) ∈
        CClosedGraphs.Peeling.maxCliquesIn G (fiberDomain G W v (sourceIndex K G W v)) :=
      source_restricted_mem_maxCliquesIn hKmem hP
    have : f K ∈ target := by
      rw [Finset.mem_sigma]
      exact ⟨by simpa [f] using hS, by simpa [f] using hL⟩
    simpa using this
  have hinj : Set.InjOn f (↑lhs : Set (Finset V)) := by
    intro K hK K' hK' hEq
    have hKfilter : K ∈ (CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y) := by simpa [lhs] using hK
    have hK'filter : K' ∈ (CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y) := by simpa [lhs] using hK'
    rcases Finset.mem_filter.mp hKfilter with ⟨hKmem, hP⟩
    rcases Finset.mem_filter.mp hK'filter with ⟨hK'mem, hP'⟩
    have hS : sourceIndex K G W v = sourceIndex K' G W v := by
      simpa [f] using congrArg Sigma.fst hEq
    have hL : K ∩ fiberFinset G W v (sourceIndex K G W v) =
        K' ∩ fiberFinset G W v (sourceIndex K' G W v) := by
      simpa [f] using congrArg Sigma.snd hEq
    have hL' : K ∩ fiberFinset G W v (sourceIndex K' G W v) =
        K' ∩ fiberFinset G W v (sourceIndex K' G W v) := by
      simpa [hS] using hL
    calc
      K = sourceIndex K G W v ∪
          (K ∩ fiberFinset G W v (sourceIndex K G W v)) :=
        (source_eq_index_union_restricted hKmem hP).symm
      _ = sourceIndex K' G W v ∪
          (K' ∩ fiberFinset G W v (sourceIndex K' G W v)) := by rw [hS, hL']
      _ = K' := source_eq_index_union_restricted hK'mem hP'
  exact Finset.card_le_card_of_injOn f hmaps hinj

/-- Rewriting the re-indexed sigma as a sum of maximal-clique counts over only
the fibres that are actually nonempty. -/
theorem card_source_le_nonempty_fiber_sum
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card ≤
      ∑ S ∈ (nbrsIn G W v).powerset.filter
          (fun S => Finset.Nonempty S ∧ (fiberFinset G W v S).Nonempty),
        CClosedGraphs.Peeling.numMaxCliquesIn G (fiberDomain G W v S) := by
  classical
  have h := card_source_le_sigma_nonempty G W hv
  rw [Finset.card_sigma] at h
  simpa [CClosedGraphs.Peeling.numMaxCliquesIn] using h

/-- Every nonempty fibre has the inherited `(c-1)`-closure property. -/
theorem fiberDomain_isCClosedOn {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V}
    {S : Finset V} (hS : S ⊆ nbrsIn G W v) {u : V} (hu : u ∈ S) :
    IsCClosedOn (c - 1) G (fiberDomain G W v S) := by
  have huW : u ∈ W :=
    (mem_nbrsInFinset.mp (by simpa [nbrsIn] using hS hu)).1
  have hclosed : IsCClosedOn (c - 1) G (W ∩ G.neighborSet u) :=
    lemma_3_2 hc hW huW
  exact isCClosedOn_mono hclosed
    (fiberDomain_subset_inter_neighborSet (G := G) (W := W) (v := v) hu)


/-- The elementary real-power inequality behind the paper's linearisation:
for `0 ≤ x ≤ d`, `d > 0`, and exponent `e ≥ 1`, one has
`x^e ≤ (x/d) d^e`. -/
theorem rpow_le_div_mul_rpow {x d e : ℝ}
    (hx : 0 ≤ x) (hd : 0 < d) (hxd : x ≤ d) (he : 1 ≤ e) :
    x ^ e ≤ (x / d) * d ^ e := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · subst x
    have he0 : e ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one he)
    rw [Real.zero_rpow he0]
    simp
  · have hpow : x ^ (e - 1) ≤ d ^ (e - 1) :=
      Real.rpow_le_rpow hx hxd (sub_nonneg.mpr he)
    have hxsplit : x ^ e = x * x ^ (e - 1) := by
      calc
        x ^ e = x ^ ((e - 1) + 1) := by ring_nf
        _ = x ^ (e - 1) * x ^ (1 : ℝ) := Real.rpow_add hxpos (e - 1) 1
        _ = x ^ (e - 1) * x := by rw [Real.rpow_one]
        _ = x * x ^ (e - 1) := by ring
    have hright : (x / d) * d ^ e = x * d ^ (e - 1) := by
      have hdsub : d ^ e = d ^ (e - 1) * d := by
        calc
          d ^ e = d ^ ((e - 1) + 1) := by ring_nf
          _ = d ^ (e - 1) * d ^ (1 : ℝ) := Real.rpow_add hd (e - 1) 1
          _ = d ^ (e - 1) * d := by rw [Real.rpow_one]
      rw [hdsub]
      field_simp [ne_of_gt hd]
    rw [hxsplit, hright]
    exact mul_le_mul_of_nonneg_left hpow hx

/-- `F0` is nonnegative at a nonnegative real base. -/
theorem F0_nonneg {m : ℝ} (hm : 0 ≤ m) (k : ℕ) : 0 ≤ F0 m k := by
  unfold F0
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hm _)

/-- `F0` is strictly positive at a positive base. -/
theorem F0_pos {m : ℝ} (hm : 0 < m) (k : ℕ) : 0 < F0 m k := by
  unfold F0
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hm _)

/-- Linearisation of `F0` for exponents corresponding to `k ≥ 1`:
`F0 x k ≤ (x/d) F0 d k` whenever `0 ≤ x ≤ d` and `d > 0`. -/
theorem F0_linearization {x d : ℝ} {k : ℕ}
    (hx : 0 ≤ x) (hd : 0 < d) (hxd : x ≤ d) (hk : 1 ≤ k) :
    F0 x k ≤ (x / d) * F0 d k := by
  let e : ℝ := 2 - (2 : ℝ) ^ (1 - (k : ℝ))
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : 1 ≤ e := by
    have hnonpos : 1 - (k : ℝ) ≤ 0 := by linarith
    have hpowle : (2 : ℝ) ^ (1 - (k : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hnonpos
    dsimp [e]
    linarith
  have hlin : x ^ e ≤ (x / d) * d ^ e :=
    rpow_le_div_mul_rpow hx hd hxd hexp
  unfold F0
  change (4 : ℝ) ^ ((((k : ℝ) + 4) * ((k : ℝ) - 1)) / 2) * x ^ e ≤
    (x / d) * ((4 : ℝ) ^ ((((k : ℝ) + 4) * ((k : ℝ) - 1)) / 2) * d ^ e)
  calc
    (4 : ℝ) ^ ((((k : ℝ) + 4) * ((k : ℝ) - 1)) / 2) * x ^ e
        ≤ (4 : ℝ) ^ ((((k : ℝ) + 4) * ((k : ℝ) - 1)) / 2) *
            ((x / d) * d ^ e) :=
          mul_le_mul_of_nonneg_left hlin (Real.rpow_nonneg (by norm_num) _)
    _ = (x / d) *
          ((4 : ℝ) ^ ((((k : ℝ) + 4) * ((k : ℝ) - 1)) / 2) * d ^ e) := by ring

/-- The strict factor comparison used at the end of Case 2. -/
theorem one_add_mul_lt_mul_two_mul {m b : ℝ} (hm : 1 ≤ m) (hb : 2 ≤ b) :
    1 + m * b < m * (2 * b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hb)]


/-- Maximal cliques through `v` are exactly the maximal cliques of the
nonempty `(c-1)`-closed neighbourhood `W ∩ N(v)`, so `hIH` bounds them by
`F0 Δ (c-1)`. -/
theorem card_through_le_F0 {c : ℕ} (hc : 2 ≤ c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔpos : 1 ≤ Δ)
    (hv_deg : (W ∩ G.neighborSet v).ncard = Δ)
    (hIH : ∀ W' : Set V, W'.Nonempty → IsCClosedOn (c - 1) G W' →
      (CClosedGraphs.Peeling.numMaxCliquesIn G W' : ℝ) ≤ F0 (W'.ncard : ℝ) (c - 1)) :
    ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K)).card : ℕ) : ℝ) ≤
      F0 (Δ : ℝ) (c - 1) := by
  classical
  let A : Set V := W ∩ G.neighborSet v
  have hDeltaPos : 0 < Δ := lt_of_lt_of_le Nat.zero_lt_one hΔpos
  have hApos : 0 < A.ncard := by
    simpa [A, hv_deg] using hDeltaPos
  have hAne : A.Nonempty := (Set.ncard_pos).mp hApos
  have hclosed : IsCClosedOn (c - 1) G A :=
    lemma_3_2 (c := c) (by omega) hW hv
  have hIH_A : (CClosedGraphs.Peeling.numMaxCliquesIn G A : ℝ) ≤
      F0 (Δ : ℝ) (c - 1) := by
    simpa [A, hv_deg] using hIH A hAne hclosed
  have hcard : ((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K)).card =
      CClosedGraphs.Peeling.numMaxCliquesIn G A := by
    simpa [A] using card_maxCliques_mem_eq G W hv
  calc
    ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K)).card : ℕ) : ℝ)
        = (CClosedGraphs.Peeling.numMaxCliquesIn G A : ℝ) := by exact_mod_cast hcard
    _ ≤ F0 (Δ : ℝ) (c - 1) := hIH_A

/-- The avoiding-`v` family is bounded by `F0 Δ (c-1)` times the paper's
min factor and `2^(c-1)`, using only nonempty fibres and induction on each. -/
theorem card_source_le_F0_mul {c : ℕ} (hc : 2 ≤ c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔpos : 1 ≤ Δ)
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ)
    (_hv_deg : (W ∩ G.neighborSet v).ncard = Δ)
    (hIH : ∀ W' : Set V, W'.Nonempty → IsCClosedOn (c - 1) G W' →
      (CClosedGraphs.Peeling.numMaxCliquesIn G W' : ℝ) ≤ F0 (W'.ncard : ℝ) (c - 1)) :
    ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ) ≤
      F0 (Δ : ℝ) (c - 1) * min (Δ : ℝ) ((W.ncard : ℝ) / (Δ : ℝ)) * 2 ^ (c - 1) := by
  classical
  let d : ℝ := (Δ : ℝ)
  let n : ℝ := (W.ncard : ℝ)
  let b : ℝ := (2 : ℝ) ^ (c - 1)
  let Fd : ℝ := F0 d (c - 1)
  let A : Finset V := nbrsIn G W v
  let idx : Finset (Finset V) :=
    A.powerset.filter (fun S => S.Nonempty ∧ (fiberFinset G W v S).Nonempty)
  let X : Finset V → Set V := fun S => fiberDomain G W v S
  let x : Finset V → ℝ := fun S => ((X S).ncard : ℝ)
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hΔpos)
  have hFdpos : 0 < Fd := by
    dsimp [Fd]
    exact F0_pos hdpos (c - 1)
  have hbnon : 0 ≤ b := by
    dsimp [b]
    positivity
  have hsum1 : ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ) ≤
      ∑ S ∈ idx, (CClosedGraphs.Peeling.numMaxCliquesIn G (X S) : ℝ) := by
    have hnat := card_source_le_nonempty_fiber_sum (G := G) (W := W) (v := v) hv
    have hreal : (((CClosedGraphs.Peeling.maxCliquesIn G W).filter
          (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card : ℝ) ≤
        ((∑ S ∈ (nbrsIn G W v).powerset.filter
          (fun S => S.Nonempty ∧ (fiberFinset G W v S).Nonempty),
          CClosedGraphs.Peeling.numMaxCliquesIn G (fiberDomain G W v S) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hnat
    simpa [A, idx, X, Nat.cast_sum] using hreal
  have hterm : ∀ S ∈ idx,
      (CClosedGraphs.Peeling.numMaxCliquesIn G (X S) : ℝ) ≤ (x S / d) * Fd := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSpow, hSne, hXneFin⟩
    have hSsub : S ⊆ A := by
      simpa [A] using Finset.mem_powerset.mp hSpow
    have hXne : (X S).Nonempty := by
      rcases hXneFin with ⟨z, hz⟩
      exact ⟨z, by simpa [X, fiberFinset, fiberDomain] using hz⟩
    rcases hSne with ⟨u, huS⟩
    have hclosed : IsCClosedOn (c - 1) G (X S) :=
      fiberDomain_isCClosedOn (c := c) (by omega) hW (v := v) hSsub huS
    have hnumIH : (CClosedGraphs.Peeling.numMaxCliquesIn G (X S) : ℝ) ≤
        F0 (x S) (c - 1) := by
      simpa [x] using hIH (X S) hXne hclosed
    have hx_nonneg : 0 ≤ x S := by
      dsimp [x]
      exact_mod_cast Nat.cast_nonneg (X S).ncard
    have hxle_nat : (X S).ncard ≤ Δ :=
      fiberDomain_ncard_le (G := G) (W := W) (v := v) hΔ hSsub huS
    have hxle : x S ≤ d := by
      dsimp [x, d]
      exact_mod_cast hxle_nat
    have hlin : F0 (x S) (c - 1) ≤ (x S / d) * Fd := by
      simpa [Fd] using F0_linearization hx_nonneg hdpos hxle (show 1 ≤ c - 1 by omega)
    exact le_trans hnumIH hlin
  have hsum2 : (∑ S ∈ idx, (CClosedGraphs.Peeling.numMaxCliquesIn G (X S) : ℝ)) ≤
      ∑ S ∈ idx, (x S / d) * Fd := Finset.sum_le_sum hterm
  have hsum3 : (∑ S ∈ idx, (x S / d) * Fd) = ((∑ S ∈ idx, x S) / d) * Fd := by
    calc
      (∑ S ∈ idx, (x S / d) * Fd) = (∑ S ∈ idx, x S / d) * Fd := by
        rw [Finset.sum_mul]
      _ = ((∑ S ∈ idx, x S) / d) * Fd := by rw [Finset.sum_div]
  let allIdx : Finset (Finset V) := A.powerset.filter (fun S => S.Nonempty)
  have hidx_sub : idx ⊆ allIdx := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSpow, hSne, _hXne⟩
    exact Finset.mem_filter.mpr ⟨hSpow, hSne⟩
  have hx_nonneg_all : ∀ S ∈ allIdx, S ∉ idx → 0 ≤ x S := by
    intro S _hS _hnot
    dsimp [x]
    exact_mod_cast Nat.cast_nonneg (X S).ncard
  have hxsum_le_full : (∑ S ∈ idx, x S) ≤ ∑ S ∈ allIdx, x S :=
    Finset.sum_le_sum_of_subset_of_nonneg hidx_sub hx_nonneg_all
  have hfull_nat := sum_commonNbrs_dist2In_le (c := c) (by omega) hW hv
  have hfull_bound : (∑ S ∈ allIdx, x S) ≤ ((dist2In G W v).ncard : ℝ) * b := by
    have hreal : ((∑ S ∈ (A.powerset.filter (fun S => S.Nonempty)),
          (commonNbrs G S ∩ dist2In G W v).ncard : ℕ) : ℝ) ≤
        (((dist2In G W v).ncard * 2 ^ (c - 1) : ℕ) : ℝ) := by
      exact_mod_cast hfull_nat
    simpa [allIdx, A, x, X, fiberDomain, b, Nat.cast_mul, Nat.cast_pow] using hreal
  have hxsum_le_N2 : (∑ S ∈ idx, x S) ≤ ((dist2In G W v).ncard : ℝ) * b :=
    le_trans hxsum_le_full hfull_bound
  have hN2le := (ineq_3 (c := c) (by omega) hW hv Δ hΔ).2
  have hN2le_sq_nat : (dist2In G W v).ncard ≤ Δ ^ 2 :=
    le_trans hN2le (min_le_left _ _)
  have hN2le_W_nat : (dist2In G W v).ncard ≤ W.ncard :=
    le_trans hN2le (min_le_right _ _)
  have hN2_div_d_le_d : ((dist2In G W v).ncard : ℝ) / d ≤ d := by
    rw [div_le_iff₀ hdpos]
    have hsq : ((dist2In G W v).ncard : ℝ) ≤ d ^ 2 := by
      dsimp [d]
      exact_mod_cast hN2le_sq_nat
    simpa [pow_two] using hsq
  have hN2_div_d_le_nd : ((dist2In G W v).ncard : ℝ) / d ≤ n / d := by
    apply div_le_div_of_nonneg_right
    · dsimp [n]
      exact_mod_cast hN2le_W_nat
    · exact le_of_lt hdpos
  have hN2_div_le_m : ((dist2In G W v).ncard : ℝ) / d ≤ min d (n / d) :=
    le_min hN2_div_d_le_d hN2_div_d_le_nd
  have hB_aux : ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ) ≤
      Fd * (((dist2In G W v).ncard : ℝ) / d) * b := by
    calc
      ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter
          (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ)
          ≤ ∑ S ∈ idx, (CClosedGraphs.Peeling.numMaxCliquesIn G (X S) : ℝ) := hsum1
      _ ≤ ∑ S ∈ idx, (x S / d) * Fd := hsum2
      _ = ((∑ S ∈ idx, x S) / d) * Fd := hsum3
      _ ≤ ((((dist2In G W v).ncard : ℝ) * b) / d) * Fd := by
          have hdiv := div_le_div_of_nonneg_right hxsum_le_N2 (le_of_lt hdpos)
          exact mul_le_mul_of_nonneg_right hdiv (le_of_lt hFdpos)
      _ = Fd * (((dist2In G W v).ncard : ℝ) / d) * b := by ring
  have hB : ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ) ≤
      Fd * min d (n / d) * b := by
    calc
      ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter
          (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ)
          ≤ Fd * (((dist2In G W v).ncard : ℝ) / d) * b := hB_aux
      _ ≤ Fd * min d (n / d) * b := by
          have hmul : Fd * (((dist2In G W v).ncard : ℝ) / d) ≤ Fd * min d (n / d) :=
            mul_le_mul_of_nonneg_left hN2_div_le_m (le_of_lt hFdpos)
          exact mul_le_mul_of_nonneg_right hmul hbnon
  simpa [Fd, d, n, b] using hB


open Classical in
/-- Case 2 of Theorem 3.1: the number of maximal cliques that contain `v` or
meet its neighbourhood is strictly below the paper's Case-2 bound. -/
theorem case_2_count {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 2 ≤ c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔpos : 1 ≤ Δ) (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ)
    (hv_deg : (W ∩ G.neighborSet v).ncard = Δ)
    (hcase : Real.sqrt (W.ncard : ℝ) < (Δ : ℝ))
    (hIH : ∀ W' : Set V, W'.Nonempty → IsCClosedOn (c - 1) G W' →
      (CClosedGraphs.Peeling.numMaxCliquesIn G W' : ℝ) ≤ F0 (W'.ncard : ℝ) (c - 1)) :
    ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter
        (fun K => v ∈ K ∨ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ) <
      F0 (Δ : ℝ) (c - 1) * min (Δ : ℝ) ((W.ncard : ℝ) / (Δ : ℝ)) * 2 ^ c := by
  classical
  have hdpos_from_hcase : (0 : ℝ) < (Δ : ℝ) :=
    lt_of_le_of_lt (Real.sqrt_nonneg (W.ncard : ℝ)) hcase
  let s : Finset (Finset V) := CClosedGraphs.Peeling.maxCliquesIn G W
  let P : Finset V → Prop := fun K => v ∈ K
  let Q : Finset V → Prop := fun K => ∃ y ∈ K, G.Adj v y
  let d : ℝ := (Δ : ℝ)
  let n : ℝ := (W.ncard : ℝ)
  let b : ℝ := (2 : ℝ) ^ (c - 1)
  let Fd : ℝ := F0 d (c - 1)
  have hsplit_set : s.filter (fun K => P K ∨ Q K) =
      s.filter P ∪ s.filter (fun K => v ∉ K ∧ Q K) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdisj : Disjoint (s.filter P) (s.filter (fun K => v ∉ K ∧ Q K)) := by
    rw [Finset.disjoint_left]
    intro K hK1 hK2
    exact (Finset.mem_filter.mp hK2).2.1 (Finset.mem_filter.mp hK1).2
  have hcard_nat : (s.filter (fun K => P K ∨ Q K)).card =
      (s.filter P).card + (s.filter (fun K => v ∉ K ∧ Q K)).card := by
    rw [hsplit_set, Finset.card_union_of_disjoint hdisj]
  have hcard_split : (((s.filter (fun K => P K ∨ Q K)).card : ℕ) : ℝ) =
      (((s.filter P).card : ℕ) : ℝ) +
        (((s.filter (fun K => v ∉ K ∧ Q K)).card : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hA : (((s.filter P).card : ℕ) : ℝ) ≤ Fd := by
    simpa [s, P, Fd, d] using
      (card_through_le_F0 (c := c) hc hW hv Δ hΔpos hv_deg hIH)
  have hB : (((s.filter (fun K => v ∉ K ∧ Q K)).card : ℕ) : ℝ) ≤
      Fd * min d (n / d) * b := by
    simpa [s, Q, Fd, d, n, b] using
      (card_source_le_F0_mul (c := c) hc hW hv Δ hΔpos hΔ hv_deg hIH)
  have hdpos : 0 < d := by
    simpa [d] using hdpos_from_hcase
  have hFdpos : 0 < Fd := by
    dsimp [Fd]
    exact F0_pos hdpos (c - 1)
  have hDeltaLeW : Δ ≤ W.ncard := by
    rw [← hv_deg]
    exact Set.ncard_le_ncard (fun x hx => hx.1)
  have hdn : d ≤ n := by
    dsimp [d, n]
    exact_mod_cast hDeltaLeW
  have hn_div_ge_one : 1 ≤ n / d := by
    rw [le_div_iff₀ hdpos]
    simpa using hdn
  have hm_ge_one : 1 ≤ min d (n / d) := by
    apply le_min
    · dsimp [d]
      exact_mod_cast hΔpos
    · exact hn_div_ge_one
  have hc1 : 1 ≤ c - 1 := by omega
  have hb_ge_two : 2 ≤ b := by
    dsimp [b]
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (c - 1) := pow_le_pow_right₀ (by norm_num) hc1
  have hfactor : 1 + min d (n / d) * b < min d (n / d) * (2 * b) :=
    one_add_mul_lt_mul_two_mul hm_ge_one hb_ge_two
  have hstrict : Fd * (1 + min d (n / d) * b) <
      Fd * (min d (n / d) * (2 * b)) :=
    mul_lt_mul_of_pos_left hfactor hFdpos
  have h2c : (2 : ℝ) ^ c = 2 * b := by
    have hcpos : 1 ≤ c := by omega
    calc
      (2 : ℝ) ^ c = (2 : ℝ) ^ ((c - 1) + 1) := by rw [Nat.sub_add_cancel hcpos]
      _ = (2 : ℝ) ^ (c - 1) * 2 := by rw [pow_succ]
      _ = 2 * b := by dsimp [b]; ring
  have hmain : (((s.filter (fun K => P K ∨ Q K)).card : ℕ) : ℝ) <
      Fd * min d (n / d) * (2 : ℝ) ^ c := by
    calc
      (((s.filter (fun K => P K ∨ Q K)).card : ℕ) : ℝ)
          = (((s.filter P).card : ℕ) : ℝ) +
              (((s.filter (fun K => v ∉ K ∧ Q K)).card : ℕ) : ℝ) := hcard_split
      _ ≤ Fd + Fd * min d (n / d) * b := add_le_add hA hB
      _ = Fd * (1 + min d (n / d) * b) := by ring
      _ < Fd * (min d (n / d) * (2 * b)) := hstrict
      _ = Fd * min d (n / d) * (2 : ℝ) ^ c := by
        rw [h2c]
        ring
  simpa [s, P, Q, Fd, d, n] using hmain

end CClosedGraphs.Improved

end Prove2SwarmSubmission

open CClosedGraphs.Improved

open Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 2 ≤ c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔpos : 1 ≤ Δ) (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ)
    (hv_deg : (W ∩ G.neighborSet v).ncard = Δ)
    (hcase : Real.sqrt (W.ncard : ℝ) < (Δ : ℝ))
    (hIH : ∀ W' : Set V, W'.Nonempty → IsCClosedOn (c - 1) G W' →
      (CClosedGraphs.Peeling.numMaxCliquesIn G W' : ℝ) ≤ F0 (W'.ncard : ℝ) (c - 1)) :
    ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K ∨ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ) <
      F0 (Δ : ℝ) (c - 1) * min (Δ : ℝ) ((W.ncard : ℝ) / (Δ : ℝ)) * 2 ^ c := by
  exact Prove2SwarmSubmission.CClosedGraphs.Improved.case_2_count hc hW hv Δ hΔpos hΔ hv_deg hcase hIH
