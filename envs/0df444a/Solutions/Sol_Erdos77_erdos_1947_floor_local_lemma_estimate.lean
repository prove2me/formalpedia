-- Prove2me | solution 1 for Erdos77.erdos_1947_floor_local_lemma_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:18:08.942497+00:00
-- url     : https://prove2.me/submissions/68c6c0ec-5f8e-4daf-84dd-28306b03cff2

import Mathlib
import Theorems.Thm_Erdos77_erdos_1947_floor_local_lemma_estimate_large

theorem solution (k : Nat) (hk : 4 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    (4 : Real) * (Nat.choose k 2 : Real) *
      (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1 := by
  by_cases hk5 : 5 <= k
  · exact Erdos77.erdos_1947_floor_local_lemma_estimate_large k hk5
  · have hk4 : k = 4 := by omega
    subst k
    norm_num [Nat.floor, Nat.choose]
