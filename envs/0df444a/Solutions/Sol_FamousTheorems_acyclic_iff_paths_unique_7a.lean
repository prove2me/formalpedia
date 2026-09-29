-- Prove2me | solution 1 for FamousTheorems.acyclic_iff_paths_unique_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:11:39.807904+00:00
-- url     : https://prove2.me/submissions/d5394502-e097-4bcd-955c-9063730e2618

import Mathlib

theorem solution {V : Type*} {G : SimpleGraph V} : G.IsAcyclic ↔ ∀ u v : V, Subsingleton (G.Path u v) :=
  SimpleGraph.isAcyclic_iff_subsingleton_path
