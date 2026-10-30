-- Prove2me | solution 1 for BitcoinDifficulty.no_wrap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:58:52.211386+00:00
-- url     : https://prove2.me/submissions/1bfa0cc2-4515-44c2-a169-a6cd717e0cee

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow
theorem solution (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (ts : Nat) (hts : ts ≤ 4838400) :
    t * ts < BitcoinPow.width := by
  calc t * ts ≤ BitcoinPow.powLimit * 4838400 := Nat.mul_le_mul ht hts
    _ < BitcoinPow.width := by unfold BitcoinPow.powLimit BitcoinPow.width; decide
