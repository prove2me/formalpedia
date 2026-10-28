-- Prove2me | solution 2 for BitcoinSer.leBytes_length
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:53:03.494984+00:00
-- url     : https://prove2.me/submissions/9f1811de-1515-4016-b946-dc3a85da7bf3

import Definitions.Def_BitcoinSer

open BitcoinSer

theorem solution (k n : Nat) : (BitcoinSer.leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]
