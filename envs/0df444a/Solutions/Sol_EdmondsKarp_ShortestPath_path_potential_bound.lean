-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.path_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:09:50.490749+00:00
-- url     : https://prove2.me/submissions/ba6d8f6f-1c85-4bdb-9d7e-e244f23e9b6b

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop)
    (d : V → ℕ∞) (hd : ∀ u v, R u v → d v ≤ d u + 1)
    (P : List V) (u v : V) (hh : P.head? = some u) (hl : P.getLast? = some v)
    (hc : P.IsChain R) : d v ≤ d u + ((pathArcs P).length : ℕ∞) := by
  induction P generalizing u with
  | nil => simp at hh
  | cons a L ih =>
    have ha : a = u := by simpa using hh
    subst u
    cases L with
    | nil =>
      have hv : a = v := by simpa using hl
      simp [pathArcs, hv]
    | cons b L =>
      have hb := ih b (by simp) (by simpa using hl) hc.tail
      have he := hd a b hc.rel
      have hlen : (pathArcs (a :: b :: L)).length = (pathArcs (b :: L)).length + 1 := by
        simp [pathArcs]
      rw [hlen, Nat.cast_add, Nat.cast_one]
      calc
        d v ≤ d b + ((pathArcs (b :: L)).length : ℕ∞) := hb
        _ ≤ (d a + 1) + ((pathArcs (b :: L)).length : ℕ∞) := add_le_add he le_rfl
        _ = d a + (((pathArcs (b :: L)).length : ℕ∞) + 1) := by ac_rfl
