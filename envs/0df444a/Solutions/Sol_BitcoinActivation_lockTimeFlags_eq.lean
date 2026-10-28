-- Prove2me | solution 1 for BitcoinActivation.lockTimeFlags_eq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:21.759303+00:00
-- url     : https://prove2.me/submissions/ec484307-ec0b-420a-bcc5-4667d9bbc7f5

import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- Sequence locks are verified exactly from the CSV activation height. -/
theorem solution (height : Nat) :
    BitcoinActivation.lockTimeFlags height =
      if 419328 ≤ height then BitcoinActivation.LOCKTIME_VERIFY_SEQUENCE else 0 := by
  unfold lockTimeFlags activeAt deploymentHeight
  simp
