-- Prove2me | solution 1 for Erdos77.spencer_1975_unordered_edge_coloring_lll_core
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T17:59:34.292825+00:00
-- url     : https://prove2.me/submissions/51128b41-e8dd-4c3c-9188-a2aed3791502

import Mathlib
import Theorems.Thm_Erdos77_spencer_1975_uniform_hyperedge_coloring_lll_core

theorem solution (V : Type*) [Fintype V] [DecidableEq V]
    (k : Nat) (hk : 2 <= k) (hkn : k <= Fintype.card V)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) *
          (Nat.choose (Fintype.card V - 2) (k - 2) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun c : {e : Finset V // e.card = 2} -> Bool =>
      forall s : Finset V, s.card = k ->
        And
          (Exists fun e : {e : Finset V // e.card = 2} =>
            And (forall v : V, v ∈ (e : Finset V) -> v ∈ s) (c e = true))
          (Exists fun e : {e : Finset V // e.card = 2} =>
            And (forall v : V, v ∈ (e : Finset V) -> v ∈ s) (c e = false)) := by
  simpa using
    (Erdos77.spencer_1975_uniform_hyperedge_coloring_lll_core
      V 2 k (by omega) hk hkn hcond)
