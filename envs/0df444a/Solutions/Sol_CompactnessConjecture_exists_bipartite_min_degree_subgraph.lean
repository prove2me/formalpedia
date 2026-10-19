-- Prove2me | solution 1 for CompactnessConjecture.exists_bipartite_min_degree_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/2e8748b6-19e7-46b5-838e-09d3c2d8fc11

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_edgeFinset_card_eq_natCard
import Theorems.Thm_CompactnessConjecture_degree_eq_natCard_neighborSet
import Theorems.Thm_CompactnessConjecture_exists_bipartite_min_degree_supported_subgraph

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ (N : ℕ) (B : SimpleGraph (Fin N)) (f : Fin N ↪ Fin n),
      0 < N ∧ N ≤ n ∧ B.IsBipartite ∧ B.map f ≤ G ∧
      G.edgeFinset.card ≤ 2 * n * B.minDegree ∧
      ∀ v : Fin N, G.edgeFinset.card ≤ 2 * n * B.degree v := by
  classical
  obtain ⟨H, hHbip, hHG, hHpositive, hminimum⟩ :=
    exists_bipartite_min_degree_supported_subgraph G hpositive
  have hsupportPositive : 0 < Nat.card H.support := by
    apply Finite.card_pos_iff.mpr
    obtain ⟨⟨edge, hedge⟩⟩ := Finite.card_pos_iff.mp hHpositive
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have huv : H.Adj u v := by
        simpa only [SimpleGraph.mem_edgeSet] using hedge
      exact ⟨⟨u, huv.mem_support_left⟩⟩
  let N := Nat.card H.support
  let supportEquiv : Fin N ≃ H.support :=
    (Finite.equivFin H.support).symm
  let f : Fin N ↪ Fin n :=
    supportEquiv.toEmbedding.trans
      (Function.Embedding.subtype (fun v : Fin n => v ∈ H.support))
  let B : SimpleGraph (Fin N) :=
    (H.induce H.support).comap supportEquiv.toEmbedding
  have hBcomap : B = H.comap f := by
    ext u v
    rfl
  have hBbip : B.IsBipartite := by
    rw [hBcomap]
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Hom.comap f H) hHbip
  have hmap : B.map f ≤ G := by
    calc
      B.map f ≤ H := by
        rw [hBcomap]
        exact SimpleGraph.map_comap_le f H
      _ ≤ G := hHG
  let supportIso : B ≃g H.induce H.support :=
    SimpleGraph.Iso.comap supportEquiv (H.induce H.support)
  have hdegrees : ∀ v : Fin N,
      G.edgeFinset.card ≤ 2 * n * B.degree v := by
    intro v
    have hdegree := hminimum (f v) (supportEquiv v).property
    have hBdegree :
        Nat.card (B.neighborSet v) =
          Nat.card (H.neighborSet (f v)) := by
      calc
        Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet
              (supportEquiv v)) := by
          change Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet (supportIso v))
          exact Nat.card_congr (supportIso.mapNeighborSet v)
        _ = Nat.card (H.neighborSet (f v)) := by
          change Nat.card ((H.induce H.support).neighborSet
            (supportEquiv v)) =
              Nat.card (H.neighborSet (supportEquiv v : Fin n))
          simpa only [degree_eq_natCard_neighborSet] using
            (SimpleGraph.degree_induce_support (G := H)
              (supportEquiv v))
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet, Fintype.card_fin, hBdegree]
      using hdegree
  have hNn : N ≤ n := by
    simpa using Fintype.card_le_of_injective f f.injective
  letI : Nonempty (Fin N) := ⟨⟨0, hsupportPositive⟩⟩
  obtain ⟨v, hv⟩ := B.exists_minimal_degree_vertex
  have hmin : G.edgeFinset.card ≤ 2 * n * B.minDegree := by
    rw [hv]
    exact hdegrees v
  exact ⟨N, B, f, hsupportPositive, hNn,
    hBbip, hmap, hmin, hdegrees⟩
end CompactnessConjecture
