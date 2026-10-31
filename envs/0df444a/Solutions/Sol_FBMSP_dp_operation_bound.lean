-- Prove2me | solution 1 for FBMSP.dp_operation_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:09:30.835342+00:00
-- url     : https://prove2.me/submissions/900e210f-9edb-4d69-92b3-25a9070a52ea

import Definitions.Def_FBMSP_DynamicProgram

open FBMSP

private theorem twice_blockOracleCalls_aux (n : ℕ) :
    2 * blockOracleCalls n = n * (n + 1) := by
  induction n with
  | zero => simp [blockOracleCalls]
  | succ n ih =>
      simp only [blockOracleCalls]
      nlinarith

private theorem blockOracleCalls_le_square_aux (n : ℕ) :
    blockOracleCalls n ≤ n * n := by
  have h := twice_blockOracleCalls_aux n
  cases n with
  | zero => simp [blockOracleCalls]
  | succ n => nlinarith

theorem solution (k n m : ℕ) (hn : 1 ≤ n) :
    tableWork k n m ≤ 4 * (n * n) * (k + m) := by
  have hbase : m * blockOracleCalls n ≤ m * (n * n) :=
    Nat.mul_le_mul_left m (blockOracleCalls_le_square_aux n)
  have hsquare : (n + 1) * (n + 1) ≤ 4 * (n * n) := by nlinarith
  have htable : tableCandidateEvaluations k n ≤ k * (4 * (n * n)) :=
    (Nat.mul_le_mul_left k (blockOracleCalls_le_square_aux (n + 1))).trans
      (Nat.mul_le_mul_left k hsquare)
  unfold tableWork
  nlinarith
