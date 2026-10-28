-- Prove2me | solution 1 for BitcoinSig.normalizeS_low
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:24.747985+00:00
-- url     : https://prove2.me/submissions/3bd07a7b-942e-42ea-82ed-fac1e74d77e4

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (s : Nat) (hs : s < BitcoinSig.n) :
    BitcoinSig.isHighS (BitcoinSig.normalizeS s) = false := by
  unfold normalizeS isHighS at *
  unfold n at *
  by_cases h : 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 / 2 < s
  · simp only [decide_eq_true h, if_true, decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false h, if_false, Bool.false_eq_true]
