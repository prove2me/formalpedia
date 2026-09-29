-- Prove2me | solution 1 for Erdos77.spencer_1975_finite_and_bad_graph_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:58:53.079984+00:00
-- url     : https://prove2.me/submissions/5b4d7c71-e5e3-4dc8-8f7d-70858383dbdb

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

open Erdos77

theorem solution (k n : Nat)
    (hfinite : ∃ m : Nat, ∀ G : SimpleGraph (Fin m),
      (∃ s : Finset (Fin m), s.card = k ∧ G.IsClique s) ∨
        (∃ s : Finset (Fin m), s.card = k ∧ (Compl.compl G).IsClique s))
    (hbad : ∃ G : SimpleGraph (Fin n),
      (¬ ∃ s : Finset (Fin n), s.card = k ∧ G.IsClique s) ∧
        (¬ ∃ s : Finset (Fin n), s.card = k ∧ (Compl.compl G).IsClique s)) :
    (n : Real) + 1 ≤ (diagonalRamsey k : Real) := by
  classical
  have hfiniteP : ∃ m : Nat, ∀ G : SimpleGraph (Fin m),
      (∃ s : Finset (Fin m), G.IsNClique k s) ∨
        (∃ s : Finset (Fin m), (Compl.compl G).IsNClique k s) := by
    rcases hfinite with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro G
    rcases hm G with ⟨s, hs, hc⟩ | ⟨s, hs, hc⟩
    · exact Or.inl ⟨s, (SimpleGraph.isNClique_iff G).2 ⟨hc, hs⟩⟩
    · exact Or.inr ⟨s, (SimpleGraph.isNClique_iff (Compl.compl G)).2 ⟨hc, hs⟩⟩
  rcases hbad with ⟨G, hG, hGc⟩
  have hGbad : ¬ ∃ s : Finset (Fin n), G.IsNClique k s := by
    intro hs
    rcases hs with ⟨s, hs⟩
    exact hG ⟨s, hs.card_eq, hs.isClique⟩
  have hGcbad : ¬ ∃ s : Finset (Fin n), (Compl.compl G).IsNClique k s := by
    intro hs
    rcases hs with ⟨s, hs⟩
    exact hGc ⟨s, hs.card_eq, hs.isClique⟩
  have hlower : ∀ m : Nat,
      (∀ H : SimpleGraph (Fin m),
        (∃ s : Finset (Fin m), H.IsNClique k s) ∨
          (∃ s : Finset (Fin m), (Compl.compl H).IsNClique k s)) → n + 1 ≤ m := by
    intro m hm
    by_contra hnot
    have hmn : m ≤ n := by omega
    let f : Fin m ↪ Fin n := ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩
    let H : SimpleGraph (Fin m) := G.comap f
    rcases hm H with ⟨s, hs⟩ | ⟨s, hs⟩
    · have htransport : G.IsNClique k (s.map f) :=
        (hs.map).mono (SimpleGraph.map_comap_le f G)
      exact hGbad ⟨s.map f, htransport⟩
    · have hEq : Compl.compl (G.comap f) = (Compl.compl G).comap f := by
        ext a b
        simp [SimpleGraph.compl_adj, SimpleGraph.comap_adj, f.injective.eq_iff]
      have hs' : ((Compl.compl G).comap f).IsNClique k s := by
        rw [← hEq]
        exact hs
      have htransport : (Compl.compl G).IsNClique k (s.map f) :=
        (hs'.map).mono (SimpleGraph.map_comap_le f (Compl.compl G))
      exact hGcbad ⟨s.map f, htransport⟩
  have hS : {m : Nat | ∀ H : SimpleGraph (Fin m),
      (∃ s : Finset (Fin m), H.IsNClique k s) ∨
        (∃ s : Finset (Fin m), (Compl.compl H).IsNClique k s)}.Nonempty := by
    rcases hfiniteP with ⟨m, hm⟩
    exact ⟨m, hm⟩
  have hNat : n + 1 ≤ sInf {m : Nat | ∀ H : SimpleGraph (Fin m),
      (∃ s : Finset (Fin m), H.IsNClique k s) ∨
        (∃ s : Finset (Fin m), (Compl.compl H).IsNClique k s)} := by
    refine le_csInf hS ?_
    intro m hm
    exact hlower m hm
  change (n : Real) + 1 ≤ (((sInf {m : Nat | ∀ H : SimpleGraph (Fin m),
      (∃ s : Finset (Fin m), H.IsNClique k s) ∨
        (∃ s : Finset (Fin m), (Compl.compl H).IsNClique k s)}) : Nat) : Real)
  exact_mod_cast hNat
