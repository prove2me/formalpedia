-- Prove2me | solution 1 for Erdos77.erdos_1947_floor_local_lemma_estimate_large
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:41:49.682076+00:00
-- url     : https://prove2.me/submissions/e418446f-0ca2-4389-bdca-ec4cdeb0ce35

import Mathlib
import Theorems.Thm_Erdos77_erdos_1947_floor_local_lemma_estimate_ge6

theorem solution (k : Nat) (hk : 5 <= k) :
    let n : Nat := Nat.floor ((2 : Real) ^ ((k : Real) / 2))
    (4 : Real) * (Nat.choose k 2 : Real) *
      (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1 := by
  by_cases hk6 : 6 <= k
  · exact Erdos77.erdos_1947_floor_local_lemma_estimate_ge6 k hk6
  · have hk5 : k = 5 := by omega
    subst k
    have hsq : (Real.sqrt 32) ^ 2 = 32 := Real.sq_sqrt (by norm_num)
    have hroot : 0 <= Real.sqrt 32 := Real.sqrt_nonneg 32
    have hpow : (2 : Real) ^ ((5 : Real) / 2) = Real.sqrt 32 := by
      rw [Real.rpow_div_two_eq_sqrt 5 (by norm_num : (0 : Real) <= 2)]
      calc
        Real.sqrt 2 ^ (5 : Real) = Real.sqrt 2 ^ (5 : Nat) := by
          exact Real.rpow_natCast (Real.sqrt 2) 5
        _ = 4 * Real.sqrt 2 := by
          calc
            Real.sqrt 2 ^ (5 : Nat) = (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 := by ring
            _ = 4 * Real.sqrt 2 := by
              have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
              rw [hs2]
              norm_num
        _ = Real.sqrt 32 := by
          have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          rw [show (32 : Real) = 16 * 2 by norm_num,
            Real.sqrt_mul (by norm_num : (0 : Real) <= 16)]
          norm_num
    have hlow : (5 : Real) <= Real.sqrt 32 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have hhi : Real.sqrt 32 < 6 :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have hfloor : Nat.floor ((2 : Real) ^ ((5 : Real) / 2)) = 5 := by
      apply (Nat.floor_eq_iff (by positivity)).2
      constructor
      · rw [hpow]
        exact hlow
      · rw [hpow]
        rw [show (↑(5 : Nat) : Real) + 1 = 6 by norm_num]
        exact hhi
    norm_num [hfloor, Nat.choose]
