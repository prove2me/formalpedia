-- Prove2me | solution 1 for Erdos77.erdos_1947_floor_spencer_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T11:58:43.695496+00:00
-- url     : https://prove2.me/submissions/1cb87202-2fd7-4c46-a28b-95a9559534a0

import Theorems.Thm_Erdos77_erdos_1947_floor_vertex_count
import Theorems.Thm_Erdos77_erdos_1947_floor_local_lemma_estimate

theorem solution (k : Nat) (hk : 4 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    And (k <= n)
      ((4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
        (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) := by
  exact And.intro
    (Erdos77.erdos_1947_floor_vertex_count k hk)
    (Erdos77.erdos_1947_floor_local_lemma_estimate k hk)
