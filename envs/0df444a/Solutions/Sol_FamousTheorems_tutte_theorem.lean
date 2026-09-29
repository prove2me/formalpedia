-- Prove2me | solution 1 for FamousTheorems.tutte_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:15:45.134573+00:00
-- url     : https://prove2.me/submissions/ee66baea-88a6-4178-84dd-21e5be4b7561

import Mathlib

theorem solution {V : Type*} {G : SimpleGraph V} [Finite V] :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔ ∀ u : Set V, ¬ G.IsTutteViolator u :=
  SimpleGraph.tutte
