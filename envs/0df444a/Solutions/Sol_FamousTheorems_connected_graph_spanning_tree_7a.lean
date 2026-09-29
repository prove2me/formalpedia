-- Prove2me | solution 1 for FamousTheorems.connected_graph_spanning_tree_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:16:28.068992+00:00
-- url     : https://prove2.me/submissions/dac04d23-9b71-4723-ba15-de06cadac3bb

import Mathlib

theorem solution {V : Type*} {G : SimpleGraph V} (hG : G.Connected) : ∃ T ≤ G, T.IsTree :=
  hG.exists_isTree_le
