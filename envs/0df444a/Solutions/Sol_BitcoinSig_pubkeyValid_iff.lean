-- Prove2me | solution 1 for BitcoinSig.pubkeyValid_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:14.930907+00:00
-- url     : https://prove2.me/submissions/1ddee53e-ca7f-4f6f-8a64-53ad79baa015

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (pk : Bytes) :
    BitcoinSig.pubkeyValid pk = true ↔
      (pk.length = 33 ∧ ((pk.getD 0 0).toNat = 2 ∨ (pk.getD 0 0).toNat = 3)) ∨
      (pk.length = 65 ∧ ((pk.getD 0 0).toNat = 4 ∨ (pk.getD 0 0).toNat = 6 ∨ (pk.getD 0 0).toNat = 7)) := by
  cases pk with
  | nil => simp [pubkeyValid]
  | cons h t =>
    simp only [pubkeyValid, pubkeyLen, List.getD_cons_zero, List.length_cons]
    by_cases h1 : BitVec.toNat h = 2 ∨ BitVec.toNat h = 3
    · simp only [if_pos h1, decide_eq_true_eq]; omega
    · simp only [if_neg h1, decide_eq_true_eq]
      by_cases h2 : BitVec.toNat h = 4 ∨ BitVec.toNat h = 6 ∨ BitVec.toNat h = 7
      · simp only [if_pos h2]; omega
      · simp only [if_neg h2]; omega
