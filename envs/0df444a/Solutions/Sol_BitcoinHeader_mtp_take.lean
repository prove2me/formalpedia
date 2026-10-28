-- Prove2me | solution 1 for BitcoinHeader.mtp_take
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:12.51828+00:00
-- url     : https://prove2.me/submissions/c2373716-46d6-4356-8d78-e3851b0bb78c

import Definitions.Def_BitcoinHeader

open BitcoinHeader

theorem solution (times : List Int) :
    BitcoinHeader.medianTimePast times = BitcoinHeader.medianTimePast (times.take BitcoinHeader.nMedianTimeSpan) := by
  unfold medianTimePast timeWindow
  rw [List.take_take, Nat.min_self]
