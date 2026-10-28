-- Prove2me | solution 1 for CClosedGraphs.Improved.ineq_2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T00:45:44.419475+00:00
-- url     : https://prove2.me/submissions/435b2d4d-8166-4aa8-849c-799a98cdc200

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

omit [DecidableEq V] in
/-- Membership normal form for the frozen maximal-clique finset. -/
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

end CClosedGraphs.Improved

end Prove2SwarmSubmission

open CClosedGraphs.Improved
open Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∉ K ∧ ∃ y ∈ K, G.Adj v y)).card ≤
      ∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        CClosedGraphs.Peeling.numMaxCliquesIn G (commonNbrs G S ∩ dist2In G W v) := by
  exact Prove2SwarmSubmission.CClosedGraphs.Improved.ineq_2 G W hv
