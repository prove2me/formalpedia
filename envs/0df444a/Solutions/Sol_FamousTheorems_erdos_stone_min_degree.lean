-- Prove2me | solution 1 for FamousTheorems.erdos_stone_min_degree
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:21:15.633532+00:00
-- url     : https://prove2.me/submissions/bf84b8d5-6d14-47f3-b2af-18b2c6980bfe

import Mathlib

theorem solution {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      (G.minDegree : ℝ) ≥ (1 - 1 / r + ε) * n → (SimpleGraph.completeEquipartiteGraph (r + 1) t).IsContained G :=
  SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree hε r t
