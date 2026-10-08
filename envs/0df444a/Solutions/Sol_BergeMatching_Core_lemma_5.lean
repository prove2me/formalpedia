-- Prove2me | solution 1 for BergeMatching.Core.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T15:08:15.075734+00:00
-- url     : https://prove2.me/submissions/c1d2f050-4303-4fcd-a104-941eb78bf421

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

open SimpleGraph

/-- Edges of `S` pairwise share no vertex. -/
private def EdgeDisj {V : Type} (S : Set (Sym2 V)) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, ∀ x, x ∈ e → x ∈ f → e = f

private lemma edgeDisj_of_isMatching {V : Type} {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : EdgeDisj M.edgeSet := by
  intro e he f hf x hxe hxf
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxf
  rw [Subgraph.mem_edgeSet] at he hf
  rw [hM.eq_of_adj_left he hf]

/-- A vertex-disjoint set of non-loop edges covers exactly twice as many vertices as it has
edges. -/
private lemma ncard_verts {V : Type} [Fintype V] [DecidableEq V] (S : Set (Sym2 V))
    (hS : EdgeDisj S) (hd : ∀ e ∈ S, ¬ e.IsDiag) :
    {x | ∃ e ∈ S, x ∈ e}.ncard = 2 * S.ncard := by
  classical
  have hset : {x | ∃ e ∈ S, x ∈ e} = ↑(S.toFinset.biUnion (fun e => e.toFinset)) := by
    ext x; simp
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion, Set.ncard_eq_toFinset_card']
  · rw [Finset.sum_congr rfl (g := fun _ => 2), Finset.sum_const, smul_eq_mul, mul_comm]
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e (hd e (by simpa using he))
  · intro e he f hf hef
    show Disjoint e.toFinset f.toFinset
    rw [Finset.disjoint_left]
    intro x hxe hxf
    simp only [Sym2.mem_toFinset] at hxe hxf
    exact hef (hS e (by simpa using he) f (by simpa using hf) x hxe hxf)

/-- A matching of `G` covers `2 |M|` vertices. -/
private lemma ncard_covered {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) :
    {x | ∃ e ∈ M.edgeSet, x ∈ e}.ncard = 2 * M.edgeSet.ncard :=
  ncard_verts _ (edgeDisj_of_isMatching hM)
    (fun _ he => G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset he))

end BergeMatching.Core

open BergeMatching.Core

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (hN : {x : V | IsNeutral M x}.ncard ≤ 1) :
    IsMaximumMatching M := by
  refine ⟨hM, fun M' hM' => ?_⟩
  -- the neutral vertices are exactly the complement of the vertices covered by `M`
  have hcompl : {x : V | IsNeutral M x} = {x | ∃ e ∈ M.edgeSet, x ∈ e}ᶜ := by
    ext x
    simp only [IsNeutral, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and]
  have hsplit := Set.ncard_add_ncard_compl {x | ∃ e ∈ M.edgeSet, x ∈ e}
  rw [← hcompl, ncard_covered hM, Nat.card_eq_fintype_card] at hsplit
  have hle : {x | ∃ e ∈ M'.edgeSet, x ∈ e}.ncard ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  rw [ncard_covered hM'] at hle
  omega
