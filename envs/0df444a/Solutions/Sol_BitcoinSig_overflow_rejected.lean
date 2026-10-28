-- Prove2me | solution 1 for BitcoinSig.overflow_rejected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:22.296197+00:00
-- url     : https://prove2.me/submissions/7336a05c-537b-4040-add1-0b96c7534c63

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (pk hash sig : Bytes) (h : BitcoinSig.parseDerLax sig = some (0, 0)) :
    BitcoinSig.pubkeyVerify pk hash sig = false := by
  unfold pubkeyVerify
  split
  · rfl
  · split
    · rfl
    · simp [h, ecdsaVerifyRaw]
