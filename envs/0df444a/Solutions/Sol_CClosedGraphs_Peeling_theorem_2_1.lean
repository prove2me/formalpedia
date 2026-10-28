-- Prove2me | solution 1 for CClosedGraphs.Peeling.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T05:28:21.090665+00:00
-- url     : https://prove2.me/submissions/a2d5ccd1-f23f-4d42-97cd-4d58b095afa2

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace Prove2SwarmSubmission

open CClosedGraphs.Peeling

/-! Verified support for the CClosedGraphs Peeling campaigns.

Two independently verified candidate bodies, unchanged and in this order:
`type_three_structure` (run com8-20261028T032428Z-a778ac8a, critic export sha256
a1c64718098ad9cf944ae5241f3565485e810467b9a45367dfe403aa81447413) and `moon_moser`
(run com8-20261028T032432Z-27685def, prover export sha256
1a10d004110a3cf4569a07751d36e608cca65d6b3e34024a2c7526b29a25f989). Their global
`solution` aliases are omitted. The proved statements are
`Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.type_three_structure` and
`Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.moon_moser`, each with the exact
frozen statement of the canonical target. Paste this whole file after the two preamble
imports of a single-file candidate; never import it as a module in a final candidate. -/

namespace Prove2SwarmVerifiedSupport

open _root_.CClosedGraphs.Peeling

set_option autoImplicit false

namespace CClosedGraphs.Peeling

open Classical
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex of `K.erase v` is adjacent to `v`. -/
private lemma erase_coe_subset_neighborSet
    {G : SimpleGraph V} {W : Set V} {v : V} {K : Finset V}
    (hK : K ∈ maxCliquesIn G W) (hvK : v ∈ K) :
    (↑(K.erase v) : Set V) ⊆ G.neighborSet v := by
  have hmax : Maximal (fun T : Finset V =>
      (↑T : Set V) ⊆ W ∧ G.IsClique (↑T : Set V)) K :=
    (Finset.mem_filter.mp hK).2
  have hcl : G.IsClique (K : Set V) := hmax.1.2
  intro x hx
  have hxerase : x ∈ K.erase v := Finset.mem_coe.mp hx
  rcases Finset.mem_erase.mp hxerase with ⟨hxv, hxK⟩
  rw [SimpleGraph.mem_neighborSet]
  exact hcl hvK hxK hxv.symm

omit [Fintype V] in
/-- Inserting a vertex adjacent to `v` and to every other vertex of `K`
preserves being a clique. -/
private lemma insert_isClique
    {G : SimpleGraph V} {v w : V} {K : Finset V}
    (hKcl : G.IsClique (K : Set V))
    (hvw : G.Adj w v)
    (hrest : ∀ x ∈ K.erase v, G.Adj w x) :
    G.IsClique ((insert w K : Finset V) : Set V) := by
  rw [Finset.coe_insert, SimpleGraph.isClique_insert]
  constructor
  · exact hKcl
  · intro x hx _
    have hxK : x ∈ K := by simpa using hx
    by_cases hxv : x = v
    · simpa [hxv] using hvw
    · exact hrest x (Finset.mem_erase.mpr ⟨hxv, hxK⟩)

/-- No vertex outside `K` can be adjacent to `v` and to every vertex of
`K.erase v`; otherwise inserting it would strictly enlarge the maximal clique. -/
private lemma no_extension
    {G : SimpleGraph V} {W : Set V} {v : V} {K : Finset V}
    (hK : K ∈ maxCliquesIn G W)
    {w : V} (hwW : w ∈ W) (hvw : G.Adj v w) (hwK : w ∉ K)
    (hrest : ∀ x ∈ K.erase v, G.Adj w x) : False := by
  have hmax : Maximal (fun T : Finset V =>
      (↑T : Set V) ⊆ W ∧ G.IsClique (↑T : Set V)) K :=
    (Finset.mem_filter.mp hK).2
  have hKW : (K : Set V) ⊆ W := hmax.1.1
  have hKcl : G.IsClique (K : Set V) := hmax.1.2
  have hinsW : ((insert w K : Finset V) : Set V) ⊆ W := by
    rw [Finset.coe_insert]
    intro x hx
    rcases hx with rfl | hxK
    · exact hwW
    · exact hKW hxK
  have hinsCl : G.IsClique ((insert w K : Finset V) : Set V) :=
    insert_isClique hKcl (G.adj_symm hvw) hrest
  have hKleIns : K ≤ insert w K := by
    intro x hx
    exact Finset.mem_insert_of_mem hx
  have hInsleK : insert w K ≤ K := hmax.2 ⟨hinsW, hinsCl⟩ hKleIns
  exact hwK (hInsleK (Finset.mem_insert_self w K))

/-- The type-3 condition supplies a non-neighbour `u` of `v` adjacent to all of
`K.erase v`. -/
private lemma exists_witness
    {G : SimpleGraph V} {W : Set V} {v : V} {K : Finset V}
    (hK : K ∈ maxCliquesIn G W)
    (h3 : K.erase v ∉ maxCliquesIn G (W \ {v})) :
    ∃ u ∈ W, u ≠ v ∧ ¬ G.Adj v u ∧
      (∀ x ∈ K.erase v, G.Adj u x) := by
  have hmax : Maximal (fun T : Finset V =>
      (↑T : Set V) ⊆ W ∧ G.IsClique (↑T : Set V)) K :=
    (Finset.mem_filter.mp hK).2
  have hKW : (K : Set V) ⊆ W := hmax.1.1
  have hKcl : G.IsClique (K : Set V) := hmax.1.2
  have hEraseSubset : (↑(K.erase v) : Set V) ⊆ W \ {v} := by
    intro x hx
    have hxerase : x ∈ K.erase v := Finset.mem_coe.mp hx
    rcases Finset.mem_erase.mp hxerase with ⟨hxv, hxK⟩
    exact ⟨hKW hxK, by simpa using hxv⟩
  have hEraseSubsetK : (↑(K.erase v) : Set V) ⊆ (K : Set V) := by
    intro x hx
    exact (Finset.mem_erase.mp (Finset.mem_coe.mp hx)).2
  have hEraseCl : G.IsClique (↑(K.erase v) : Set V) := hKcl.subset hEraseSubsetK
  have hpErase : (fun T : Finset V => (↑T : Set V) ⊆ W \ {v} ∧
      G.IsClique (↑T : Set V)) (K.erase v) := ⟨hEraseSubset, hEraseCl⟩
  have hnotmax : ¬ Maximal (fun T : Finset V => (↑T : Set V) ⊆ W \ {v} ∧
      G.IsClique (↑T : Set V)) (K.erase v) := by
    intro hmaxE
    apply h3
    rw [maxCliquesIn, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmaxE⟩
  have hnotforall : ¬ (∀ T : Finset V,
      ((↑T : Set V) ⊆ W \ {v} ∧ G.IsClique (↑T : Set V)) →
      K.erase v ≤ T → T ≤ K.erase v) := by
    intro hforall
    exact hnotmax ⟨hpErase, hforall⟩
  rw [not_forall] at hnotforall
  rcases hnotforall with ⟨T, hT⟩
  rw [Classical.not_imp] at hT
  rcases hT with ⟨hTprop, hTnot⟩
  rw [Classical.not_imp] at hTnot
  rcases hTnot with ⟨hle, hnotle⟩
  have hTsub : (↑T : Set V) ⊆ W \ {v} := hTprop.1
  have hTcl : G.IsClique (↑T : Set V) := hTprop.2
  change ¬ T ⊆ K.erase v at hnotle
  rcases Finset.not_subset.mp hnotle with ⟨u, huT, hunotE⟩
  have huW' : u ∈ W \ {v} := hTsub huT
  have huW : u ∈ W := huW'.1
  have huv : u ≠ v := by
    simpa using huW'.2
  have huK : u ∉ K := by
    intro huK
    exact hunotE (Finset.mem_erase.mpr ⟨huv, huK⟩)
  have huAdj : ∀ x ∈ K.erase v, G.Adj u x := by
    intro x hx
    have hxT : x ∈ T := hle hx
    exact hTcl huT hxT (by rintro rfl; exact hunotE hx)
  have hnonadj : ¬ G.Adj v u := by
    intro hvu
    exact no_extension hK huW hvu huK huAdj
  exact ⟨u, huW, huv, hnonadj, huAdj⟩

/-- `K.erase v` is maximal inside the common neighbourhood of the witness `u`
and `v`. -/
private lemma erase_maximal
    {G : SimpleGraph V} {W : Set V} {v : V} {K : Finset V} {u : V}
    (hK : K ∈ maxCliquesIn G W)
    (hEraseSubsetNbr : (↑(K.erase v) : Set V) ⊆ G.neighborSet v)
    (huAdj : ∀ x ∈ K.erase v, G.Adj u x) :
    K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u) := by
  have hmax : Maximal (fun T : Finset V =>
      (↑T : Set V) ⊆ W ∧ G.IsClique (↑T : Set V)) K :=
    (Finset.mem_filter.mp hK).2
  have hKW : (K : Set V) ⊆ W := hmax.1.1
  have hKcl : G.IsClique (K : Set V) := hmax.1.2
  have hEraseSubsetK : (↑(K.erase v) : Set V) ⊆ (K : Set V) := by
    intro x hx
    exact (Finset.mem_erase.mp (Finset.mem_coe.mp hx)).2
  have hEraseCl : G.IsClique (↑(K.erase v) : Set V) := hKcl.subset hEraseSubsetK
  have hEraseSubset : (↑(K.erase v) : Set V) ⊆
      W ∩ G.commonNeighbors v u := by
    intro x hx
    have hxerase : x ∈ K.erase v := Finset.mem_coe.mp hx
    have hxK : x ∈ K := (Finset.mem_erase.mp hxerase).2
    have hxW : x ∈ W := hKW hxK
    have hvn : G.Adj v x :=
      (SimpleGraph.mem_neighborSet G v x).mp (hEraseSubsetNbr hx)
    have hun : G.Adj u x := huAdj x hxerase
    exact ⟨hxW, (SimpleGraph.mem_commonNeighbors G).mpr ⟨hvn, hun⟩⟩
  rw [maxCliquesIn, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  constructor
  · exact ⟨hEraseSubset, hEraseCl⟩
  · intro T hT hle y hyT
    have hTsub : (↑T : Set V) ⊆ W ∩ G.commonNeighbors v u := hT.1
    have hTcl : G.IsClique (↑T : Set V) := hT.2
    have hyW : y ∈ W := (hTsub hyT).1
    have hyCommon : y ∈ G.commonNeighbors v u := (hTsub hyT).2
    have hvy : G.Adj v y :=
      ((SimpleGraph.mem_commonNeighbors G).mp hyCommon).1
    have hyK : y ∈ K := by
      by_contra hyK
      have hrest : ∀ x ∈ K.erase v, G.Adj y x := by
        intro x hx
        have hxT : x ∈ T := hle hx
        refine hTcl hyT hxT ?_
        intro hyx
        apply hyK
        rw [← hyx] at hx
        exact (Finset.mem_erase.mp hx).2
      exact no_extension hK hyW hvy hyK hrest
    have hyv : y ≠ v := by
      have hne : v ≠ y := G.ne_of_adj hvy
      exact hne.symm
    exact Finset.mem_erase.mpr ⟨hyv, hyK⟩

theorem type_three_structure {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) (_hv : v ∈ W) (K : Finset V) (hK : K ∈ maxCliquesIn G W)
    (hvK : v ∈ K) (h3 : K.erase v ∉ maxCliquesIn G (W \ {v})) :
    (↑(K.erase v) : Set V) ⊆ G.neighborSet v ∧
    (∀ w ∈ W ∩ G.neighborSet v, w ∉ K → ¬ ∀ x ∈ K.erase v, G.Adj w x) ∧
    ∃ u ∈ W, u ≠ v ∧ ¬ G.Adj v u ∧ (∀ x ∈ K.erase v, G.Adj u x) ∧
      K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u) := by
  have hA : (↑(K.erase v) : Set V) ⊆ G.neighborSet v :=
    erase_coe_subset_neighborSet hK hvK
  have hB : ∀ w ∈ W ∩ G.neighborSet v, w ∉ K →
      ¬ ∀ x ∈ K.erase v, G.Adj w x := by
    intro w hw hwK hrest
    exact no_extension hK hw.1
      ((SimpleGraph.mem_neighborSet G v w).mp hw.2) hwK hrest
  rcases exists_witness hK h3 with ⟨u, huW, huv, hnonadj, huAdj⟩
  exact ⟨hA, hB, u, huW, huv, hnonadj, huAdj, erase_maximal hK hA huAdj⟩

end CClosedGraphs.Peeling

open _root_.CClosedGraphs.Peeling

set_option autoImplicit false

namespace CClosedGraphs.Peeling
namespace MoonMoser

open Classical
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma mem_maxCliquesIn_iff {G : SimpleGraph V} {W : Set V} {K : Finset V} :
    K ∈ maxCliquesIn G W ↔
      (↑K : Set V) ⊆ W ∧ G.IsClique (↑K : Set V) ∧
      ∀ ⦃T : Finset V⦄, (↑T : Set V) ⊆ W →
        G.IsClique (↑T : Set V) → K ⊆ T → T ⊆ K := by
  classical
  rw [maxCliquesIn]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [Maximal]
  constructor
  · rintro ⟨⟨hKW, hKclique⟩, hKmax⟩
    exact ⟨hKW, hKclique, fun T hTW hTclique hKT => hKmax ⟨hTW, hTclique⟩ hKT⟩
  · rintro ⟨hKW, hKclique, hKmax⟩
    exact ⟨⟨hKW, hKclique⟩, fun T hT hKT => hKmax hT.1 hT.2 hKT⟩

omit [DecidableEq V] in
lemma maxCliquesIn_empty (G : SimpleGraph V) :
    maxCliquesIn G (∅ : Set V) = {∅} := by
  classical
  ext K
  rw [mem_maxCliquesIn_iff]
  constructor
  · rintro ⟨hKW, -, -⟩
    rw [Finset.mem_singleton]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    exact hKW (by exact_mod_cast hx)
  · intro hK
    rw [Finset.mem_singleton] at hK
    subst K
    simp

lemma ncard_inter_add_ncard_diff (s t : Set V) :
    (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card',
    Set.ncard_eq_toFinset_card']
  rw [Set.toFinset_inter, Set.toFinset_sdiff]
  exact Finset.card_inter_add_card_sdiff s.toFinset t.toFinset

lemma exists_mem_diff_neighborSet_of_mem_maxCliquesIn {G : SimpleGraph V} {W : Set V} {v : V}
    (hvW : v ∈ W) {K : Finset V} (hK : K ∈ maxCliquesIn G W) :
    ∃ u ∈ W \ G.neighborSet v, u ∈ K := by
  classical
  by_contra h
  rw [not_exists] at h
  rw [mem_maxCliquesIn_iff] at hK
  rcases hK with ⟨hKW, hKclique, hKmax⟩
  have hKsubN : (↑K : Set V) ⊆ G.neighborSet v := by
    intro x hxK
    by_contra hxN
    apply h x
    exact ⟨⟨hKW (by exact_mod_cast hxK), hxN⟩, by exact_mod_cast hxK⟩
  have hvK : v ∉ K := by
    intro hvKin
    have : v ∈ G.neighborSet v := hKsubN (by exact_mod_cast hvKin)
    exact G.irrefl this
  let T : Finset V := insert v K
  have hTdom : (↑T : Set V) ⊆ W := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hxK
    · exact hvW
    · exact hKW (by exact_mod_cast hxK)
  have hTclique : G.IsClique (↑T : Set V) := by
    dsimp [T]
    rw [Finset.coe_insert]
    exact hKclique.insert (fun x hx _ => hKsubN (by exact_mod_cast hx))
  have hTK : T ⊆ K := hKmax hTdom hTclique (Finset.subset_insert _ _)
  exact hvK (hTK (by simp [T]))


omit [Fintype V] in
lemma card_le_sum_card_filter (s : Finset (Finset V)) (D : Finset V)
    (h : ∀ K ∈ s, ∃ u ∈ D, u ∈ K) :
    s.card ≤ ∑ u ∈ D, (s.filter (fun K => u ∈ K)).card := by
  classical
  calc
    s.card ≤ (D.biUnion (fun u => s.filter (fun K => u ∈ K))).card := by
      apply Finset.card_le_card
      intro K hK
      rw [Finset.mem_biUnion]
      rcases h K hK with ⟨u, huD, huK⟩
      exact ⟨u, huD, by simp [hK, huK]⟩
    _ ≤ ∑ u ∈ D, (s.filter (fun K => u ∈ K)).card :=
      Finset.card_biUnion_le


lemma erase_mem_maxCliquesIn_neighborSet {G : SimpleGraph V} {W : Set V} {v : V}
    {K : Finset V}
    (hK : K ∈ (maxCliquesIn G W).filter (fun K => v ∈ K)) :
    K.erase v ∈ maxCliquesIn G (W ∩ G.neighborSet v) := by
  classical
  have hKmem : K ∈ maxCliquesIn G W := (Finset.mem_filter.mp hK).1
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
      exact hTclique.insert (fun x hx _ =>
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

lemma insert_mem_maxCliquesIn_of_mem_neighborSet {G : SimpleGraph V} {W : Set V} {v : V}
    {L : Finset V}
    (hL : L ∈ maxCliquesIn G (W ∩ G.neighborSet v))
    (hvW : v ∈ W) :
    insert v L ∈ maxCliquesIn G W := by
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
    exact hLclique.insert (fun x hx _ =>
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

theorem card_maxCliques_mem_eq (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((maxCliquesIn G W).filter (fun K => v ∈ K)).card =
      numMaxCliquesIn G (W ∩ G.neighborSet v) := by
  classical
  rw [numMaxCliquesIn]
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


lemma nat_cube_le_three_pow (m : ℕ) : m ^ 3 ≤ 3 ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 3
    · interval_cases m <;> norm_num
    · have hm3 : 3 ≤ m := by omega
      have hprev : (m - 1) ^ 3 ≤ 3 ^ (m - 1) := ih (m - 1) (by omega)
      have hmul : m ^ 3 ≤ 3 * (m - 1) ^ 3 := by
        have hcast : (m : ℤ) ^ 3 ≤ 3 * ((m - 1 : ℕ) : ℤ) ^ 3 := by
          have hsub : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
          rw [hsub]
          ring_nf
          nlinarith [sq_nonneg ((m : ℤ) - 3), sq_nonneg ((m : ℤ) - 4)]
        exact_mod_cast hcast
      calc
        m ^ 3 ≤ 3 * (m - 1) ^ 3 := hmul
        _ ≤ 3 * 3 ^ (m - 1) := Nat.mul_le_mul_left 3 hprev
        _ = 3 ^ m := by
          rw [show 3 * 3 ^ (m - 1) = 3 ^ ((m - 1) + 1) by
            rw [pow_succ]
            ring]
          rw [show (m - 1) + 1 = m by omega]

lemma natCast_le_three_rpow_div_three (m : ℕ) :
    (m : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 3) := by
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hb_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 3) :=
    Real.rpow_nonneg (by norm_num) _
  have hcube_nat : (m : ℝ) ^ 3 ≤ (3 : ℝ) ^ m := by
    exact_mod_cast nat_cube_le_three_pow m
  have hrhs : ((3 : ℝ) ^ ((m : ℝ) / 3)) ^ 3 = (3 : ℝ) ^ m := by
    have hstep : ((3 : ℝ) ^ ((m : ℝ) / 3)) ^ 3 = (3 : ℝ) ^ (m : ℝ) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ ((m : ℝ) / 3)) 3]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    exact hstep.trans (Real.rpow_natCast (3 : ℝ) m)
  apply (pow_le_pow_iff_left₀ hm_nonneg hb_nonneg (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hrhs]
  exact hcube_nat

lemma mul_rpow_le_of_le (d k : ℕ) (h : d ≤ k) :
    (d : ℝ) * (3 : ℝ) ^ ((((k - d : ℕ) : ℝ)) / 3) ≤
      (3 : ℝ) ^ ((k : ℝ) / 3) := by
  have hcast : ((k - d : ℕ) : ℝ) = (k : ℝ) - (d : ℝ) := Nat.cast_sub h
  rw [hcast]
  have hd := natCast_le_three_rpow_div_three d
  have hfac_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (((k : ℝ) - (d : ℝ)) / 3) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (d : ℝ) * (3 : ℝ) ^ (((k : ℝ) - (d : ℝ)) / 3)
        ≤ (3 : ℝ) ^ ((d : ℝ) / 3) *
            (3 : ℝ) ^ (((k : ℝ) - (d : ℝ)) / 3) :=
          mul_le_mul_of_nonneg_right hd hfac_nonneg
    _ = (3 : ℝ) ^ ((d : ℝ) / 3 + ((k : ℝ) - (d : ℝ)) / 3) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = (3 : ℝ) ^ ((k : ℝ) / 3) := by
          congr 1
          ring


theorem moon_moser_aux (G : SimpleGraph V) (W : Set V) :
    (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ W : Set V, W.ncard = k →
      (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3)
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro W hWk
      by_cases hWempty : W = ∅
      · subst W
        rw [numMaxCliquesIn, maxCliquesIn_empty]
        norm_num
      · have hWne : W.Nonempty := Set.nonempty_iff_ne_empty.mpr hWempty
        rcases Finset.exists_min_image W.toFinset
            (fun u => (W \ G.neighborSet u).ncard)
            (by simpa [Set.toFinset_nonempty] using hWne) with ⟨v, hvF, hvmin⟩
        have hvW : v ∈ W := by simpa using hvF
        have hmin : ∀ u ∈ W, (W \ G.neighborSet v).ncard ≤
            (W \ G.neighborSet u).ncard := by
          intro u hu
          exact hvmin u (by simpa using hu)
        let D : Set V := W \ G.neighborSet v
        have hvD : v ∈ D := by
          dsimp [D]
          refine ⟨hvW, ?_⟩
          rw [SimpleGraph.mem_neighborSet]
          exact G.irrefl
        have hDpos : 0 < D.ncard := (Set.ncard_pos (s := D)).mpr ⟨v, hvD⟩
        have hDleW : D ⊆ W := Set.sdiff_subset
        have hDleK : D.ncard ≤ k := by
          rw [← hWk]
          exact Set.ncard_le_ncard hDleW
        let Df : Finset V := D.toFinset
        have hDfcard_nat : Df.card = D.ncard := by
          dsimp [Df]
          exact (Set.ncard_eq_toFinset_card' D).symm
        have hcover : ∀ K ∈ maxCliquesIn G W, ∃ u ∈ D, u ∈ K := by
          intro K hK
          exact exists_mem_diff_neighborSet_of_mem_maxCliquesIn hvW hK
        have hcoverF : ∀ K ∈ maxCliquesIn G W, ∃ u ∈ Df, u ∈ K := by
          intro K hK
          rcases hcover K hK with ⟨u, huD, huK⟩
          exact ⟨u, by simpa [Df] using huD, huK⟩
        have hunion : (maxCliquesIn G W).card ≤
            ∑ u ∈ Df,
              ((maxCliquesIn G W).filter (fun K => u ∈ K)).card :=
          card_le_sum_card_filter (maxCliquesIn G W) Df hcoverF
        have hfiber : ∀ u ∈ Df,
            ((maxCliquesIn G W).filter (fun K => u ∈ K)).card =
              numMaxCliquesIn G (W ∩ G.neighborSet u) := by
          intro u hu
          exact card_maxCliques_mem_eq G W (by
            have huD : u ∈ D := by simpa [Df] using hu
            exact huD.1)
        have hterm : ∀ u ∈ Df,
            (numMaxCliquesIn G (W ∩ G.neighborSet u) : ℝ) ≤
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
          intro u hu
          have huD : u ∈ D := by simpa [Df] using hu
          have huW : u ∈ W := huD.1
          have hminu : D.ncard ≤ (W \ G.neighborSet u).ncard := by
            dsimp [D] at huD
            exact hmin u huW
          have hsplit : (W ∩ G.neighborSet u).ncard +
              (W \ G.neighborSet u).ncard = W.ncard :=
            ncard_inter_add_ncard_diff W (G.neighborSet u)
          have hA_le_k : (W ∩ G.neighborSet u).ncard ≤ k - D.ncard := by
            rw [← hWk]
            omega
          have hlt : (W ∩ G.neighborSet u).ncard < k := by
            have hkpos : 0 < k := by
              rw [← hWk]
              exact (Set.ncard_pos (s := W)).mpr hWne
            omega
          calc
            (numMaxCliquesIn G (W ∩ G.neighborSet u) : ℝ)
                ≤ (3 : ℝ) ^ (((W ∩ G.neighborSet u).ncard : ℝ) / 3) :=
                  ih (W ∩ G.neighborSet u).ncard hlt
                    (W ∩ G.neighborSet u) rfl
            _ ≤ (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
                  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
                  apply div_le_div_of_nonneg_right
                  · exact_mod_cast hA_le_k
                  · norm_num
        have hunionR : ((maxCliquesIn G W).card : ℝ) ≤
            ∑ u ∈ Df,
              (((maxCliquesIn G W).filter (fun K => u ∈ K)).card : ℝ) := by
          exact_mod_cast hunion
        have hsum_le : (∑ u ∈ Df,
              (((maxCliquesIn G W).filter (fun K => u ∈ K)).card : ℝ)) ≤
            ∑ u ∈ Df,
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [hfiber u hu]
          exact hterm u hu
        have hsum_const : (∑ u ∈ Df,
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3)) =
            (D.ncard : ℝ) * (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          exact_mod_cast hDfcard_nat
        calc
          (numMaxCliquesIn G W : ℝ) = ((maxCliquesIn G W).card : ℝ) := rfl
          _ ≤ ∑ u ∈ Df,
              (((maxCliquesIn G W).filter (fun K => u ∈ K)).card : ℝ) := hunionR
          _ ≤ ∑ u ∈ Df,
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := hsum_le
          _ = (D.ncard : ℝ) *
              (3 : ℝ) ^ ((((k - D.ncard : ℕ) : ℝ)) / 3) := hsum_const
          _ ≤ (3 : ℝ) ^ ((k : ℝ) / 3) :=
                mul_rpow_le_of_le D.ncard k hDleK
          _ = (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by rw [hWk]
  exact hP W.ncard W rfl


end MoonMoser

/-- Moon--Moser bound for the number of maximal cliques of a finite induced subgraph,
with the real exponent exactly as in the frozen target. -/
theorem moon_moser {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) :
    (numMaxCliquesIn G W : ℝ) ≤ (3 : ℝ) ^ ((W.ncard : ℝ) / 3) := by
  exact MoonMoser.moon_moser_aux G W

end CClosedGraphs.Peeling

end Prove2SwarmVerifiedSupport

/-! ## peel_step

Types 1 and 2 inject into the maximal cliques of `G[W \ {v}]` by `K ↦ K.erase v`
(`peel_typeA_card_le`). Type 3 is covered by the pieces given by the support's
`type_three_structure`, each bounded by its `moon_moser` (`peel_typeB_card_le`). -/

open _root_.CClosedGraphs.Peeling

namespace CClosedGraphs.Peeling

/-- Two maximal cliques of `G[W]` with `K ⊆ L` coincide. -/
lemma peelA_eq_of_subset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Set V} {K L : Finset V}
    (hK : K ∈ maxCliquesIn G W) (hL : L ∈ maxCliquesIn G W) (hKL : K ⊆ L) : K = L := by
  obtain ⟨_, _, hKmax⟩ :=
    Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.MoonMoser.mem_maxCliquesIn_iff.mp hK
  obtain ⟨hLW, hLcl, _⟩ :=
    Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.MoonMoser.mem_maxCliquesIn_iff.mp hL
  exact Finset.Subset.antisymm hKL (hKmax hLW hLcl hKL)

/-- A maximal clique of `G[W]` that avoids `v` is a maximal clique of `G[W \ {v}]`. -/
lemma peelA_mem_sdiff_of_notMem {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Set V} {v : V} {K : Finset V}
    (hK : K ∈ maxCliquesIn G W) (hvK : v ∉ K) : K ∈ maxCliquesIn G (W \ {v}) := by
  obtain ⟨hKW, hKcl, hKmax⟩ :=
    Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.MoonMoser.mem_maxCliquesIn_iff.mp hK
  refine Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.MoonMoser.mem_maxCliquesIn_iff.mpr
    ⟨?_, hKcl, ?_⟩
  · intro x hx
    refine Set.mem_sdiff_singleton.mpr ⟨hKW hx, ?_⟩
    rintro rfl
    exact hvK (Finset.mem_coe.mp hx)
  · intro T hTW hTcl hKT
    exact hKmax (fun x hx => Set.mem_of_mem_sdiff (hTW hx)) hTcl hKT

/-- `K ↦ K.erase v` is injective on the maximal cliques of `G[W]`. -/
lemma peelA_erase_injOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) :
    Set.InjOn (fun K : Finset V => K.erase v) (↑(maxCliquesIn G W) : Set (Finset V)) := by
  intro K hK L hL hKL
  have hK' : K ∈ maxCliquesIn G W := Finset.mem_coe.mp hK
  have hL' : L ∈ maxCliquesIn G W := Finset.mem_coe.mp hL
  have hE : K.erase v = L.erase v := hKL
  by_cases hvK : v ∈ K
  · by_cases hvL : v ∈ L
    · calc
        K = insert v (K.erase v) := (Finset.insert_erase hvK).symm
        _ = insert v (L.erase v) := by rw [hE]
        _ = L := Finset.insert_erase hvL
    · refine (peelA_eq_of_subset hL' hK' ?_).symm
      intro x hx
      have hxv : x ≠ v := by
        rintro rfl
        exact hvL hx
      have hx' : x ∈ K.erase v := by
        rw [hE]
        exact Finset.mem_erase.mpr ⟨hxv, hx⟩
      exact (Finset.mem_erase.mp hx').2
  · refine peelA_eq_of_subset hK' hL' ?_
    intro x hx
    have hxv : x ≠ v := by
      rintro rfl
      exact hvK hx
    have hx' : x ∈ L.erase v := by
      rw [← hE]
      exact Finset.mem_erase.mpr ⟨hxv, hx⟩
    exact (Finset.mem_erase.mp hx').2

/-- Types 1 and 2: `K ↦ K.erase v` injects the maximal cliques of `G[W]` that avoid `v`, or
whose deletion stays maximal, into the maximal cliques of `G[W \ {v}]`. -/
theorem peel_typeA_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) (v : V) :
    ((maxCliquesIn G W).filter
        (fun K : Finset V => v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v}))).card ≤
      numMaxCliquesIn G (W \ {v}) := by
  rw [numMaxCliquesIn]
  refine Finset.card_le_card_of_injOn (fun K : Finset V => K.erase v) ?_ ?_
  · intro K hK
    obtain ⟨hKM, hKp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hK)
    show K.erase v ∈ maxCliquesIn G (W \ {v})
    rcases hKp with hvK | hE
    · rw [Finset.erase_eq_of_notMem hvK]
      exact peelA_mem_sdiff_of_notMem hKM hvK
    · exact hE
  · intro K hK L hL hKL
    exact peelA_erase_injOn G W v
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hK)).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hL)).1) hKL

/-- One piece of the type-3 cover: the cliques of `B` whose deletion is maximal in the common
neighbourhood of `v` and a non-neighbour `u` number at most `3 ^ ((c - 1) / 3)`. -/
lemma peelB_ap_piece_card_le {V : Type*} [Fintype V] [DecidableEq V] (c : ℕ) (hc : 0 < c)
    (G : SimpleGraph V) (W : Set V) (v : V) (hv : v ∈ W)
    (hbad : ∀ w : V, ¬ IsBadPairIn c G W v w) (B : Finset (Finset V))
    (hB : ∀ K ∈ B, K ∈ maxCliquesIn G W) {u : V} (huW : u ∈ W) (huv : u ≠ v)
    (hnadj : ¬ G.Adj v u) :
    ((B.filter (fun K : Finset V =>
        K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u))).card : ℝ) ≤
      (3 : ℝ) ^ (((c : ℝ) - 1) / 3) := by
  have hlt : (W ∩ G.commonNeighbors v u).ncard < c := by
    by_contra hge
    exact hbad u ⟨hv, huW, fun hvu => huv hvu.symm, hnadj, not_lt.mp hge⟩
  have hpred : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := Nat.cast_pred hc
  have hle : ((W ∩ G.commonNeighbors v u).ncard : ℝ) ≤ (c : ℝ) - 1 := by
    rw [← hpred]
    exact Nat.cast_le.mpr (by omega)
  have hinj : (B.filter (fun K : Finset V =>
      K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u))).card ≤
      (maxCliquesIn G (W ∩ G.commonNeighbors v u)).card := by
    refine Finset.card_le_card_of_injOn (fun K : Finset V => K.erase v) ?_ ?_
    · intro K hK
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hK)).2
    · intro K hK L hL hKL
      exact peelA_erase_injOn G W v
        (Finset.mem_coe.mpr (hB K (Finset.mem_filter.mp (Finset.mem_coe.mp hK)).1))
        (Finset.mem_coe.mpr (hB L (Finset.mem_filter.mp (Finset.mem_coe.mp hL)).1)) hKL
  have hnum : numMaxCliquesIn G (W ∩ G.commonNeighbors v u) =
      (maxCliquesIn G (W ∩ G.commonNeighbors v u)).card := rfl
  calc
    ((B.filter (fun K : Finset V =>
        K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u))).card : ℝ)
        ≤ (numMaxCliquesIn G (W ∩ G.commonNeighbors v u) : ℝ) := by
          rw [hnum]
          exact_mod_cast hinj
    _ ≤ (3 : ℝ) ^ (((W ∩ G.commonNeighbors v u).ncard : ℝ) / 3) :=
          Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.moon_moser G
            (W ∩ G.commonNeighbors v u)
    _ ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (div_le_div_of_nonneg_right hle (by norm_num))

/-- Type 3: a family `B` of maximal cliques of `G[W]` that contain `v` and whose deletion is not
maximal in `G[W \ {v}]` has at most `3 ^ ((c - 1) / 3) * |W|` members. -/
lemma peelB_ap_card_le {V : Type*} [Fintype V] [DecidableEq V] (c : ℕ) (hc : 0 < c)
    (G : SimpleGraph V) (W : Set V) (v : V) (hv : v ∈ W)
    (hbad : ∀ w : V, ¬ IsBadPairIn c G W v w) (B : Finset (Finset V))
    (hB : ∀ K ∈ B, K ∈ maxCliquesIn G W ∧ v ∈ K ∧ K.erase v ∉ maxCliquesIn G (W \ {v})) :
    (B.card : ℝ) ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ) := by
  obtain ⟨U, hU⟩ : ∃ U : Finset V, ∀ u, u ∈ U ↔ u ∈ W ∧ u ≠ v ∧ ¬ G.Adj v u := by
    classical
    exact ⟨Finset.univ.filter (fun u => u ∈ W ∧ u ≠ v ∧ ¬ G.Adj v u), fun u =>
      ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩⟩⟩
  have hcover : B ⊆ U.biUnion (fun u => B.filter (fun K : Finset V =>
      K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u))) := by
    intro K hK
    obtain ⟨hKM, hvK, h3⟩ := hB K hK
    obtain ⟨_, _, u, huW, huv, hnadj, _, hmax⟩ :=
      Prove2SwarmVerifiedSupport.CClosedGraphs.Peeling.type_three_structure G W v hv K hKM hvK h3
    exact Finset.mem_biUnion.mpr
      ⟨u, (hU u).mpr ⟨huW, huv, hnadj⟩, Finset.mem_filter.mpr ⟨hK, hmax⟩⟩
  have hsum : B.card ≤ ∑ u ∈ U, (B.filter (fun K : Finset V =>
      K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u))).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hpiece : ∀ u ∈ U, ((B.filter (fun K : Finset V =>
      K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u))).card : ℝ) ≤
        (3 : ℝ) ^ (((c : ℝ) - 1) / 3) := by
    intro u hu
    obtain ⟨huW, huv, hnadj⟩ := (hU u).mp hu
    exact peelB_ap_piece_card_le c hc G W v hv hbad B (fun K hK => (hB K hK).1) huW huv hnadj
  have hUW : (U.card : ℝ) ≤ (W.ncard : ℝ) := by
    have hsub : (↑U : Set V) ⊆ W := fun x hx => ((hU x).mp (Finset.mem_coe.mp hx)).1
    have hle : (↑U : Set V).ncard ≤ W.ncard := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset] at hle
    exact_mod_cast hle
  have hX : (0 : ℝ) ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) := Real.rpow_nonneg (by norm_num) _
  calc
    (B.card : ℝ)
        ≤ ∑ u ∈ U, ((B.filter (fun K : Finset V =>
            K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u))).card : ℝ) := by
          exact_mod_cast hsum
    _ ≤ ∑ _u ∈ U, (3 : ℝ) ^ (((c : ℝ) - 1) / 3) := Finset.sum_le_sum hpiece
    _ = (U.card : ℝ) * (3 : ℝ) ^ (((c : ℝ) - 1) / 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (W.ncard : ℝ) * (3 : ℝ) ^ (((c : ℝ) - 1) / 3) := mul_le_mul_of_nonneg_right hUW hX
    _ = (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ) := mul_comm _ _

/-- Type 3 in the interface shape: the complementary filter of `peel_typeA_card_le`. -/
theorem peel_typeB_card_le {V : Type*} [Fintype V] [DecidableEq V] (c : ℕ) (hc : 0 < c)
    (G : SimpleGraph V) (W : Set V) (v : V) (hv : v ∈ W)
    (hbad : ∀ w : V, ¬ IsBadPairIn c G W v w) :
    (((maxCliquesIn G W).filter
        (fun K : Finset V => ¬ (v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v})))).card : ℝ) ≤
      (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ) := by
  refine peelB_ap_card_le c hc G W v hv hbad _ ?_
  intro K hK
  obtain ⟨hKM, hKp⟩ := Finset.mem_filter.mp hK
  refine ⟨hKM, ?_, fun hE => hKp (Or.inr hE)⟩
  by_contra hvK
  exact hKp (Or.inl hvK)

theorem peel_step {V : Type*} [Fintype V] [DecidableEq V] (c : ℕ) (hc : 0 < c)
    (G : SimpleGraph V) (W : Set V) (v : V) (hv : v ∈ W)
    (hbad : ∀ w : V, ¬ IsBadPairIn c G W v w) :
    (numMaxCliquesIn G W : ℝ) ≤
      (numMaxCliquesIn G (W \ {v}) : ℝ) + (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ) := by
  have hsplit : ((maxCliquesIn G W).filter
        (fun K : Finset V => v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v}))).card +
      ((maxCliquesIn G W).filter
        (fun K : Finset V => ¬ (v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v})))).card =
      (maxCliquesIn G W).card :=
    Finset.card_filter_add_card_filter_not _
  calc
    (numMaxCliquesIn G W : ℝ) = ((maxCliquesIn G W).card : ℝ) := rfl
    _ = (((maxCliquesIn G W).filter
            (fun K : Finset V => v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v}))).card : ℝ) +
        (((maxCliquesIn G W).filter
            (fun K : Finset V => ¬ (v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v})))).card : ℝ) := by
          exact_mod_cast hsplit.symm
    _ ≤ (numMaxCliquesIn G (W \ {v}) : ℝ) + (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ) :=
          add_le_add (by exact_mod_cast peel_typeA_card_le G W v)
            (peel_typeB_card_le c hc G W v hv hbad)

end CClosedGraphs.Peeling


set_option autoImplicit false

namespace CClosedGraphs.Peeling

open Finset

/-! ## Closure implies the absence of bad pairs -/

lemma ncard_commonNeighbors_lt_of_not_adj {V : Type*} [Fintype V]
    {c : ℕ} {G : SimpleGraph V} (hG : IsCClosed c G)
    {u v : V} (huv : u ≠ v) (hna : ¬ G.Adj u v) :
    (G.commonNeighbors u v).ncard < c := by
  by_contra hnot
  have hle : c ≤ (G.commonNeighbors u v).ncard := Nat.le_of_not_gt hnot
  exact hna (hG u v huv hle)

lemma inter_commonNeighbors_subset_commonNeighbors {V : Type*}
    (G : SimpleGraph V) (W : Set V) (u v : V) :
    W ∩ G.commonNeighbors u v ⊆ G.commonNeighbors u v := by
  intro x hx
  exact hx.2

lemma not_isBadPairIn_of_isCClosed {V : Type*} [Fintype V]
    {c : ℕ} {G : SimpleGraph V} (hG : IsCClosed c G)
    (W : Set V) (u v : V) : ¬ IsBadPairIn c G W u v := by
  intro hbad
  rcases hbad with ⟨huW, hvW, huv, hna, hle⟩
  have hlt := ncard_commonNeighbors_lt_of_not_adj hG huv hna
  have hsub := inter_commonNeighbors_subset_commonNeighbors G W u v
  have hcard : (W ∩ G.commonNeighbors u v).ncard ≤
      (G.commonNeighbors u v).ncard := Set.ncard_le_ncard hsub
  omega

lemma forall_not_isBadPairIn_of_isCClosed {V : Type*} [Fintype V]
    {c : ℕ} {G : SimpleGraph V} (hG : IsCClosed c G) :
    ∀ (W : Set V) (u v : V), ¬ IsBadPairIn c G W u v := by
  intro W u v
  exact not_isBadPairIn_of_isCClosed hG W u v

/-! ## Elementary real arithmetic and the singleton base -/

lemma three_rpow_exponent_nonneg (c : ℕ) (hc : 0 < c) :
    0 ≤ (((c : ℝ) - 1) / 3) := by
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have h3 : (0 : ℝ) < 3 := by norm_num
  exact div_nonneg (sub_nonneg.mpr hcR) h3.le

lemma one_le_three_rpow (c : ℕ) (hc : 0 < c) :
    (1 : ℝ) ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) := by
  exact Real.one_le_rpow (by norm_num) (three_rpow_exponent_nonneg c hc)

lemma peel_recurrence_real (A : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    A * ((((k - 1 : ℕ) : ℝ) * (k : ℝ)) / 2) + A * (k : ℝ) =
      A * (((k : ℝ) * ((k : ℝ) + 1)) / 2) := by
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hkcast]
  ring

lemma peel_recurrence_real' (A : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    A * ((((k - 1 : ℕ) : ℝ) * (((k - 1 : ℕ) : ℝ) + 1)) / 2) +
        A * (k : ℝ) =
      A * (((k : ℝ) * ((k : ℝ) + 1)) / 2) := by
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hkcast]
  ring

lemma nat_mul_succ_div_two_le_sq (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) * ((n : ℝ) + 1)) / 2 ≤ (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
    mul_nonneg hnR.le (sub_nonneg.mpr hn1)
  have hdiv : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    div_nonneg hnonneg (by norm_num)
  nlinarith

lemma ncard_univ_fin (n : ℕ) : (Set.univ : Set (Fin n)).ncard = n := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma maxCliquesIn_singleton {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n) :
    maxCliquesIn G ({w} : Set (Fin n)) = {{w}} := by
  classical
  ext K
  simp only [maxCliquesIn, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hmax
    have hsingleton :
        (({w} : Finset (Fin n)) : Set (Fin n)) ⊆ ({w} : Set (Fin n)) ∧
          G.IsClique (({w} : Finset (Fin n)) : Set (Fin n)) := by
      simp
    exact (maximal_iff.mp hmax).2 hsingleton (by
      intro x hx
      simpa using hmax.1.1 hx)
  · intro hK
    subst K
    rw [maximal_iff]
    constructor
    · simp
    · intro T hT hsub
      have hTsub : T ⊆ ({w} : Finset (Fin n)) := by
        intro x hx
        simpa using (hT.1 (by simpa using hx))
      exact Finset.Subset.antisymm hsub hTsub

lemma numMaxCliquesIn_singleton {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n) :
    numMaxCliquesIn G ({w} : Set (Fin n)) = 1 := by
  classical
  simp [numMaxCliquesIn, maxCliquesIn_singleton]

theorem numMaxCliquesIn_bound_of_peel
    (c n : ℕ) (hc : 0 < c) (G : SimpleGraph (Fin n))
    (hG : IsCClosed c G)
    (hpeel : ∀ (W : Set (Fin n)) (v : Fin n), v ∈ W →
      (∀ w, ¬ IsBadPairIn c G W v w) →
      (numMaxCliquesIn G W : ℝ) ≤
        (numMaxCliquesIn G (W \ {v}) : ℝ) +
          (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ)) :
    ∀ W : Set (Fin n), W.Nonempty →
      (numMaxCliquesIn G W : ℝ) ≤
        (3 : ℝ) ^ (((c : ℝ) - 1) / 3) *
          (((W.ncard : ℝ) * ((W.ncard : ℝ) + 1)) / 2) := by
  classical
  let A : ℝ := (3 : ℝ) ^ (((c : ℝ) - 1) / 3)
  have hA1 : (1 : ℝ) ≤ A := by
    dsimp [A]
    exact one_le_three_rpow c hc
  have hmain : ∀ k : ℕ, ∀ W : Set (Fin n), W.Nonempty → W.ncard = k →
      (numMaxCliquesIn G W : ℝ) ≤
        A * (((W.ncard : ℝ) * ((W.ncard : ℝ) + 1)) / 2) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro W hWne hWk
      by_cases hk1 : k = 1
      · have hWcard : W.ncard = 1 := by simpa [hk1] using hWk
        obtain ⟨w, hW⟩ := Set.ncard_eq_one.mp hWcard
        subst W
        simp only [numMaxCliquesIn_singleton, Set.ncard_singleton, Nat.cast_one]
        norm_num
        exact hA1
      · have hkpos : 0 < k := by
          rw [← hWk]
          exact (Set.ncard_pos (s := W)).mpr hWne
        have hk2 : 2 ≤ k := by omega
        obtain ⟨v, hv⟩ := hWne
        have hrest_card : (W \ {v}).ncard = k - 1 := by
          rw [Set.ncard_sdiff_singleton_of_mem hv, hWk]
        have hrest_ne : (W \ {v}).Nonempty := by
          have hpos : 0 < (W \ {v}).ncard := by
            rw [hrest_card]
            omega
          exact (Set.ncard_pos (s := W \ {v})).mp hpos
        have hlt : (W \ {v}).ncard < k := by
          rw [hrest_card]
          omega
        have hIH := ih (W \ {v}).ncard hlt (W \ {v}) hrest_ne rfl
        have hnoBad : ∀ w, ¬ IsBadPairIn c G W v w :=
          forall_not_isBadPairIn_of_isCClosed hG W v
        have hp := hpeel W v hv hnoBad
        have hstep :
            (numMaxCliquesIn G W : ℝ) ≤
              A * ((((W \ {v}).ncard : ℝ) *
                    (((W \ {v}).ncard : ℝ) + 1)) / 2) +
                A * (k : ℝ) := by
          calc
            (numMaxCliquesIn G W : ℝ)
                ≤ (numMaxCliquesIn G (W \ {v}) : ℝ) +
                    A * (W.ncard : ℝ) := by simpa [A] using hp
            _ = (numMaxCliquesIn G (W \ {v}) : ℝ) +
                    A * (k : ℝ) := by rw [hWk]
            _ ≤ A * ((((W \ {v}).ncard : ℝ) *
                      (((W \ {v}).ncard : ℝ) + 1)) / 2) +
                    A * (k : ℝ) := by
                  exact add_le_add (by simpa [A] using hIH) le_rfl
        calc
          (numMaxCliquesIn G W : ℝ)
              ≤ A * ((((W \ {v}).ncard : ℝ) *
                    (((W \ {v}).ncard : ℝ) + 1)) / 2) +
                  A * (k : ℝ) := hstep
          _ = A * (((k : ℝ) * ((k : ℝ) + 1)) / 2) := by
                rw [hrest_card]
                exact peel_recurrence_real' A k (by omega)
          _ = A * (((W.ncard : ℝ) * ((W.ncard : ℝ) + 1)) / 2) := by
                rw [hWk]
  intro W hWne
  simpa [A] using hmain W.ncard W hWne rfl

theorem theorem_2_1_of_peel (c n : ℕ) (hc : 0 < c) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : IsCClosed c G)
    (hpeel : ∀ (W : Set (Fin n)) (v : Fin n), v ∈ W →
      (∀ w, ¬ IsBadPairIn c G W v w) →
      (numMaxCliquesIn G W : ℝ) ≤
        (numMaxCliquesIn G (W \ {v}) : ℝ) +
          (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (W.ncard : ℝ)) :
    (numMaxCliques G : ℝ) ≤
      (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (n : ℝ) ^ 2 := by
  classical
  let A : ℝ := (3 : ℝ) ^ (((c : ℝ) - 1) / 3)
  have huniv_ne : (Set.univ : Set (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, by simp⟩
  have hmain := numMaxCliquesIn_bound_of_peel c n hc G hG hpeel Set.univ huniv_ne
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (by norm_num) _
  calc
    (numMaxCliques G : ℝ) = (numMaxCliquesIn G Set.univ : ℝ) := rfl
    _ ≤ A * (((n : ℝ) * ((n : ℝ) + 1)) / 2) := by
          simpa [A, ncard_univ_fin] using hmain
    _ ≤ A * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (nat_mul_succ_div_two_le_sq n hn) hA_nonneg
    _ = (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (n : ℝ) ^ 2 := by rfl

end CClosedGraphs.Peeling

/-! ## Integration: the frozen `theorem_2_1`

Assembled by graph-scout %72 from pieces pasted unchanged above: the verified peeling
support (sha256 08fddf26), the peel_step chain of the source with sha256
744c37a7, and the conditional `theorem_2_1_of_peel` of the source with sha256
58e2c5c4. Nothing here is verified until root's fresh check passes. -/

namespace CClosedGraphs.Peeling
theorem theorem_2_1 (c n : ℕ) (hc : 0 < c) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hG : IsCClosed c G) :
    (numMaxCliques G : ℝ) ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (n : ℝ) ^ 2 := by
  exact theorem_2_1_of_peel c n hc hn G hG (fun W v hv hb => peel_step c hc G W v hv hb)
end CClosedGraphs.Peeling

end Prove2SwarmSubmission

open CClosedGraphs.Peeling

theorem solution (c n : ℕ) (hc : 0 < c) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hG : IsCClosed c G) :
    (numMaxCliques G : ℝ) ≤ (3 : ℝ) ^ (((c : ℝ) - 1) / 3) * (n : ℝ) ^ 2 := by
  exact Prove2SwarmSubmission.CClosedGraphs.Peeling.theorem_2_1 c n hc hn G hG
