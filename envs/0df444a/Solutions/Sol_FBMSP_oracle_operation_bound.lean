-- Prove2me | solution 1 for FBMSP.oracle_operation_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:12:06.869954+00:00
-- url     : https://prove2.me/submissions/c22ca995-f2f4-4c75-8d6c-712906c84d23

import Definitions.Def_FBMSP_DynamicProgram

open FBMSP
open scoped BigOperators

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

private theorem oracleCharges_le_aux (charge : ℕ → ℕ → ℕ) (m : ℕ) :
    ∀ n, (∀ a b, a < b → b ≤ n → charge a b ≤ m) →
      oracleCharges charge n ≤ m * blockOracleCalls n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [oracleCharges, blockOracleCalls]
  | succ n ih =>
      intro hCost
      have hprev : oracleCharges charge n ≤ m * blockOracleCalls n :=
        ih (fun a b hab hbn => hCost a b hab (hbn.trans (Nat.le_succ n)))
      have hlast : (∑ a ∈ Finset.range (n + 1), charge a (n + 1)) ≤ (n + 1) * m := by
        calc
          (∑ a ∈ Finset.range (n + 1), charge a (n + 1)) ≤
              ∑ _a ∈ Finset.range (n + 1), m :=
            Finset.sum_le_sum (fun a ha => hCost a (n + 1) (Finset.mem_range.mp ha) le_rfl)
          _ = (n + 1) * m := by simp
      simp only [oracleCharges, blockOracleCalls]
      nlinarith

theorem solution (n k m : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (charge : ℕ → ℕ → ℕ)
    (hCost : ∀ a b, a < b → b ≤ n → charge a b ≤ m) :
    oracleCharges charge n ≤ m * blockOracleCalls n ∧
      segmentationWork charge k n ≤ 5 * (n * n) * (k + m) := by
  have hcharge := oracleCharges_le_aux charge m n hCost
  refine ⟨hcharge, ?_⟩
  have hbase : oracleCharges charge n ≤ m * (n * n) :=
    hcharge.trans (Nat.mul_le_mul_left m (blockOracleCalls_le_square_aux n))
  have hsquare : (n + 1) * (n + 1) ≤ 4 * (n * n) := by nlinarith
  have htable : tableCandidateEvaluations (k - 1) n ≤ k * (4 * (n * n)) := by
    calc
      tableCandidateEvaluations (k - 1) n ≤
          (k - 1) * ((n + 1) * (n + 1)) :=
        Nat.mul_le_mul_left (k - 1) (blockOracleCalls_le_square_aux (n + 1))
      _ ≤ k * ((n + 1) * (n + 1)) :=
        Nat.mul_le_mul_right _ (Nat.sub_le k 1)
      _ ≤ k * (4 * (n * n)) := Nat.mul_le_mul_left k hsquare
  have hback : k ≤ (n * n) * k := by
    have hn2 : 1 ≤ n * n := by nlinarith
    simpa only [one_mul] using Nat.mul_le_mul_right k hn2
  unfold segmentationWork
  nlinarith
