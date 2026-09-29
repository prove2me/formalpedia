-- Prove2me | solution 1 for FamousTheorems.euler_trail_odd_degree_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:01:25.966063+00:00
-- url     : https://prove2.me/submissions/13abdf99-a685-46cf-a884-1640f9874435

import Mathlib

theorem solution {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (hp : p.IsEulerian) :
    Fintype.card ({w : V | Odd (G.degree w)} : Set V) = 0 ∨ Fintype.card ({w : V | Odd (G.degree w)} : Set V) = 2 :=
  hp.card_odd_degree
