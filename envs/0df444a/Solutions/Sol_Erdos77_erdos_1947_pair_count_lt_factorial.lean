-- Prove2me | solution 1 for Erdos77.erdos_1947_pair_count_lt_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:26:37.558022+00:00
-- url     : https://prove2.me/submissions/80d3680b-4816-45de-b6d9-249912b736a7

import Mathlib

private theorem factorial_lower_k (k : Nat) (hk : 6 <= k) :
    k <= (k - 2).factorial := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk6 : k = 6
      · subst k
        norm_num
      · have hk7 : 7 <= k := by omega
        have hprev : 6 <= k - 1 := by omega
        have hi := ih (k - 1) (by omega) hprev
        have hfact : (k - 2).factorial = (k - 2) * (k - 3).factorial := by
          rw [show k - 2 = (k - 3) + 1 by omega, Nat.factorial_succ]
        rw [hfact]
        have hmul : (k - 2) * (k - 1) <= (k - 2) * (k - 3).factorial :=
          Nat.mul_le_mul_left (k - 2) hi
        have hprod1 : 2 * (k - 1) <= (k - 2) * (k - 1) :=
          Nat.mul_le_mul_right (k - 1) (by omega)
        have hprod2 : k <= 2 * (k - 1) := by omega
        have hbase : k <= (k - 2) * (k - 1) := hprod2.trans hprod1
        exact hbase.trans hmul

theorem solution (k : Nat) (hk : 6 <= k) :
    (Nat.choose k 2 : Real) < (Nat.factorial (k - 2) : Real) := by
  have hnat : Nat.choose k 2 < (k - 2).factorial := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hk6 : k = 6
        · subst k
          norm_num [Nat.choose]
        · have hk7 : 7 <= k := by omega
          have hprev : 6 <= k - 1 := by omega
          have hi := ih (k - 1) (by omega) hprev
          have hlower := factorial_lower_k (k - 1) hprev
          have hrec : Nat.choose k 2 = Nat.choose (k - 1) 2 + (k - 1) := by
            rw [show k = (k - 1) + 1 by omega]
            rw [Nat.choose_succ_succ' (k - 1) 1]
            simp only [show 1 + 1 = 2 by rfl,
              show k - 1 + 1 - 1 = k - 1 by omega]
            rw [Nat.choose_one_right, Nat.add_comm]
          have hfact : (k - 2).factorial = (k - 2) * (k - 3).factorial := by
            rw [show k - 2 = (k - 3) + 1 by omega, Nat.factorial_succ]
          rw [hrec, hfact]
          have hsum : Nat.choose (k - 1) 2 + (k - 1) <
              2 * (k - 3).factorial := by
            calc
              _ < (k - 3).factorial + (k - 3).factorial := Nat.add_lt_add_of_lt_of_le hi hlower
              _ = 2 * (k - 3).factorial := by omega
          have hmul : 2 * (k - 3).factorial <= (k - 2) * (k - 3).factorial :=
            Nat.mul_le_mul_right _ (by omega)
          exact hsum.trans_le hmul
  exact_mod_cast hnat
