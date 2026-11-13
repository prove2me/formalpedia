-- Prove2me | solution 1 for DirKECC1549.Main.induced_walk_lift
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T09:51:54.998208+00:00
-- url     : https://prove2.me/submissions/0b603a86-a342-42be-bc18-86ce5f46e68e

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (S : Finset (Fin n)) (x y : Fin n) (hx : x ∈ S) (hy : y ∈ S)
    (p : List (Fin m)) (hp : IsWalk G x p y)
    (he : ∀ e ∈ p, (G e).1 ∈ S ∧ (G e).2 ∈ S) :
    ∃ q : List (Fin (inducedEdges G S).card),
      q.map (fun i ↦ ((inducedEdges G S).orderIsoOfFin rfl i).1) = p ∧
      IsWalk (induced G S) (posIn S x hx) q (posIn S y hy) := by
  induction hp with
  | nil =>
    exact ⟨[], rfl, IsWalk.nil _⟩
  | @cons u v e p htail hw ih =>
    have he' : (G e).1 ∈ S ∧ (G e).2 ∈ S := he e (by simp)
    have hmem : e ∈ inducedEdges G S := by simp [inducedEdges, he']
    let i := ((inducedEdges G S).orderIsoOfFin rfl).symm ⟨e, hmem⟩
    have hi : (((inducedEdges G S).orderIsoOfFin rfl) i).1 = e := by
      simp [i]
    have hrest : ∀ a ∈ p, (G a).1 ∈ S ∧ (G a).2 ∈ S := by
      intro a ha
      exact he a (by simp [ha])
    obtain ⟨q, hq, hwalk⟩ := ih he'.2 hy hrest
    refine ⟨i :: q, ?_, ?_⟩
    · change (((inducedEdges G S).orderIsoOfFin rfl i).1) ::
          q.map (fun j ↦ ((inducedEdges G S).orderIsoOfFin rfl j).1) = e :: p
      rw [hi, hq]
    · apply IsWalk.cons i q
      · simp [induced, hi, htail]
      · simpa [induced, hi] using hwalk
