-- Prove2me | solution 1 for FamousTheorems.bridge_iff_no_cycle_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:12:45.307903+00:00
-- url     : https://prove2.me/submissions/4619f8eb-f077-419b-97a0-c6bb8e2b0a09

import Mathlib

theorem solution {V : Type*} {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeSet) :
    G.IsBridge e ↔ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges :=
  SimpleGraph.isBridge_iff_forall_cycle_notMem he
