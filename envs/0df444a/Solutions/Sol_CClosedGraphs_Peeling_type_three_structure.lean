-- Prove2me | solution 1 for CClosedGraphs.Peeling.type_three_structure
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T03:40:51.24368+00:00
-- url     : https://prove2.me/submissions/ecf47692-e1d5-4742-8cc3-790919f15423

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace Prove2SwarmSubmission

open CClosedGraphs.Peeling

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

end Prove2SwarmSubmission

open CClosedGraphs.Peeling

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) (hv : v ∈ W) (K : Finset V) (hK : K ∈ maxCliquesIn G W)
    (hvK : v ∈ K) (h3 : K.erase v ∉ maxCliquesIn G (W \ {v})) :
    (↑(K.erase v) : Set V) ⊆ G.neighborSet v ∧
    (∀ w ∈ W ∩ G.neighborSet v, w ∉ K → ¬ ∀ x ∈ K.erase v, G.Adj w x) ∧
    ∃ u ∈ W, u ≠ v ∧ ¬ G.Adj v u ∧ (∀ x ∈ K.erase v, G.Adj u x) ∧
      K.erase v ∈ maxCliquesIn G (W ∩ G.commonNeighbors v u) := by
  exact Prove2SwarmSubmission.CClosedGraphs.Peeling.type_three_structure G W v hv K hK hvK h3
