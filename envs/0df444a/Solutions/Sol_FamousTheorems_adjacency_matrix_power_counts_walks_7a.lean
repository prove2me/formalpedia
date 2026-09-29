-- Prove2me | solution 1 for FamousTheorems.adjacency_matrix_power_counts_walks_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:09:51.261463+00:00
-- url     : https://prove2.me/submissions/971646a4-fb74-42cc-aaab-e14cdc7b78c3

import Mathlib

theorem solution {α V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype V] [DecidableEq V] [Semiring α]
    (n : ℕ) (u v : V) : (G.adjMatrix α ^ n) u v = Fintype.card {p : G.Walk u v | p.length = n} :=
  SimpleGraph.adjMatrix_pow_apply_eq_card_walk n u v
