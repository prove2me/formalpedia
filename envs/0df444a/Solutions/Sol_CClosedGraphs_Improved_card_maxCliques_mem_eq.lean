-- Prove2me | solution 1 for CClosedGraphs.Improved.card_maxCliques_mem_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T00:33:45.26204+00:00
-- url     : https://prove2.me/submissions/29f0d958-93a4-4035-a58b-0f94b647e10d

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace Prove2SwarmSubmission
open CClosedGraphs.Improved

set_option autoImplicit false

namespace CClosedGraphs.Improved

open Classical
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {W : Set V} {v : V}

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

end CClosedGraphs.Improved

end Prove2SwarmSubmission

open CClosedGraphs.Improved
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Set V) {v : V} (hv : v ∈ W) :
    ((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K)).card =
      CClosedGraphs.Peeling.numMaxCliquesIn G (W ∩ G.neighborSet v) := by
  exact Prove2SwarmSubmission.CClosedGraphs.Improved.card_maxCliques_mem_eq G W hv
