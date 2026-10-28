-- Prove2me | solution 1 for BitcoinSubsidy.issuance_total
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:51.208935+00:00
-- url     : https://prove2.me/submissions/40ced1d5-0665-4ff1-b6fb-cfa990c27798

import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

/-- Within one interval the subsidy is constant. -/
private theorem subsidy_in_interval (m j : Nat) (hj : j < halvingInterval) :
    coreSubsidy (halvingInterval * m + j) = (50 * COIN) / 2 ^ m := by
  rw [BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  have : (halvingInterval * m + j) / halvingInterval = m := by
    rw [Nat.mul_add_div (by decide : 0 < halvingInterval), Nat.div_eq_of_lt hj, Nat.add_zero]
  rw [this]

private theorem issued_partial (m j : Nat) (hj : j ≤ halvingInterval) :
    issuedBelow (halvingInterval * m + j) = issuedBelow (halvingInterval * m) + j * ((50 * COIN) / 2 ^ m) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, issuedBelow, ih (Nat.le_of_succ_le hj),
      subsidy_in_interval m j (Nat.lt_of_succ_le hj), Nat.add_mul, Nat.one_mul, Nat.add_assoc]

private theorem issued_intervals (m : Nat) :
    issuedBelow (halvingInterval * m) = halvingInterval * intervalSum m := by
  induction m with
  | zero => simp [issuedBelow, intervalSum]
  | succ m ih =>
    rw [Nat.mul_succ, issued_partial m halvingInterval (Nat.le_refl _), ih, intervalSum, Nat.mul_add]

theorem solution : issuedBelow zeroHeight = 2099999997690000 := by
  have h := issued_intervals 33
  have hz : zeroHeight = halvingInterval * 33 := by decide
  rw [hz, h]
  decide
