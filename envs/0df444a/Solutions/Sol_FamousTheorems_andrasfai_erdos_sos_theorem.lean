-- Prove2me | solution 1 for FamousTheorems.andrasfai_erdos_sos_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:20:28.004916+00:00
-- url     : https://prove2.me/submissions/9ecf617d-7fcd-4b84-bc63-09d9cf0a4e33

import Mathlib

theorem solution {α : Type*} [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj] {r : ℕ} (hG : G.CliqueFree (r + 1))
    (hd : (3 * r - 4) * Fintype.card α / (3 * r - 1) < G.minDegree) : G.Colorable r :=
  SimpleGraph.colorable_of_cliqueFree_lt_minDegree hG hd
