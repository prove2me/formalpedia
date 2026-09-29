-- Prove2me | solution 1 for FamousTheorems.laplacian_kernel_connected_components
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:18:35.930985+00:00
-- url     : https://prove2.me/submissions/883f3bbc-2bea-4c11-9981-975c5a5e8e56

import Mathlib

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card G.ConnectedComponent = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) :=
  SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix G
