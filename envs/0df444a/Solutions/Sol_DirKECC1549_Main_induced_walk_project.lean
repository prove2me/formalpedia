-- Prove2me | solution 1 for DirKECC1549.Main.induced_walk_project
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T09:55:37.634484+00:00
-- url     : https://prove2.me/submissions/2c855f08-16d8-4654-a24c-21a911206429

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false
open DirKECC1549.Main

private theorem project_walk {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (S : Finset (Fin n)) {a b : Fin S.card}
    {q : List (Fin (inducedEdges G S).card)} (h : IsWalk (induced G S) a q b) :
    IsWalk G (vertexOf S a)
      (q.map (fun i ↦ ((inducedEdges G S).orderIsoOfFin rfl i).1)) (vertexOf S b) := by
  induction h with
  | nil => exact IsWalk.nil _
  | @cons u v e p ht hw ih =>
    apply IsWalk.cons
    · have hh := congrArg (vertexOf S) ht
      simpa [induced, vertexOf, posIn] using hh
    · simpa [induced, vertexOf, posIn] using ih

theorem solution {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (S : Finset (Fin n)) (x y : Fin n) (hx : x ∈ S) (hy : y ∈ S)
    (q : List (Fin (inducedEdges G S).card))
    (hq : IsWalk (induced G S) (posIn S x hx) q (posIn S y hy)) :
    IsWalk G x (q.map (fun i ↦ ((inducedEdges G S).orderIsoOfFin rfl i).1)) y := by
  simpa [vertexOf, posIn] using project_walk G S hq
