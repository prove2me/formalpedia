-- Prove2me | solution 1 for Brocard.berndt_galway_block_0
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:32.809587+00:00
-- url     : https://prove2.me/submissions/7f784709-a078-4ae7-9a9d-863817fdcd4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_001
import Theorems.Thm_Brocard_berndt_galway_group_002
import Theorems.Thm_Brocard_berndt_galway_group_003
import Theorems.Thm_Brocard_berndt_galway_group_004
import Theorems.Thm_Brocard_berndt_galway_group_005
import Theorems.Thm_Brocard_berndt_galway_group_006
import Theorems.Thm_Brocard_berndt_galway_group_007
import Theorems.Thm_Brocard_berndt_galway_group_008
import Theorems.Thm_Brocard_berndt_galway_group_009
import Theorems.Thm_Brocard_berndt_galway_group_010
import Theorems.Thm_Brocard_berndt_galway_group_011
import Theorems.Thm_Brocard_berndt_galway_group_012

theorem solution (n m : ℕ) (hn : n < 10 ^ 8) (h : Nat.factorial n + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by
  have hB : (10 : ℕ) ^ 8 = 100000000 := by norm_num
  rw [hB] at hn
  rcases Nat.lt_or_ge n 8 with h0 | h0
  · -- n < 8: the known solutions (the pilot's small7, inline)
    have hm : m < 72 := by
      by_contra hc
      have e1 : 72 * 72 ≤ m ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
      have e2 : Nat.factorial n ≤ Nat.factorial 7 := Nat.factorial_le (by omega)
      have e3 : Nat.factorial 7 = 5040 := by decide
      omega
    interval_cases n <;> simp only [Nat.factorial] at h <;> interval_cases m <;> omega
  · -- 8 <= n < 10^8: the 12 groups
    exfalso
    have h1 : 8 ≤ n := h0
    have h2 : n < 100000000 := hn
    rcases Nat.lt_or_ge n 50359716 with hs0 | hs0
    · -- n < 50359716
      rcases Nat.lt_or_ge n 25359718 with hs1 | hs1
      · -- n < 25359718
        rcases Nat.lt_or_ge n 16906481 with hs2 | hs2
        · -- n < 16906481
          rcases Nat.lt_or_ge n 8453244 with hs3 | hs3
          · -- n < 8453244
            exact Brocard.berndt_galway_group_001 n m (by omega) (by omega) h
          · -- n >= 8453244
            exact Brocard.berndt_galway_group_002 n m (by omega) (by omega) h
        · -- n >= 16906481
          exact Brocard.berndt_galway_group_003 n m (by omega) (by omega) h
      · -- n >= 25359718
        rcases Nat.lt_or_ge n 42086335 with hs2 | hs2
        · -- n < 42086335
          rcases Nat.lt_or_ge n 33812954 with hs3 | hs3
          · -- n < 33812954
            exact Brocard.berndt_galway_group_004 n m (by omega) (by omega) h
          · -- n >= 33812954
            exact Brocard.berndt_galway_group_005 n m (by omega) (by omega) h
        · -- n >= 42086335
          exact Brocard.berndt_galway_group_006 n m (by omega) (by omega) h
    · -- n >= 50359716
      rcases Nat.lt_or_ge n 75179858 with hs1 | hs1
      · -- n < 75179858
        rcases Nat.lt_or_ge n 66906477 with hs2 | hs2
        · -- n < 66906477
          rcases Nat.lt_or_ge n 58633096 with hs3 | hs3
          · -- n < 58633096
            exact Brocard.berndt_galway_group_007 n m (by omega) (by omega) h
          · -- n >= 58633096
            exact Brocard.berndt_galway_group_008 n m (by omega) (by omega) h
        · -- n >= 66906477
          exact Brocard.berndt_galway_group_009 n m (by omega) (by omega) h
      · -- n >= 75179858
        rcases Nat.lt_or_ge n 91726619 with hs2 | hs2
        · -- n < 91726619
          rcases Nat.lt_or_ge n 83453238 with hs3 | hs3
          · -- n < 83453238
            exact Brocard.berndt_galway_group_010 n m (by omega) (by omega) h
          · -- n >= 83453238
            exact Brocard.berndt_galway_group_011 n m (by omega) (by omega) h
        · -- n >= 91726619
          exact Brocard.berndt_galway_group_012 n m (by omega) (by omega) h
