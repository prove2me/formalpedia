-- Prove2me | solution 1 for BitcoinBlockV2.acceptHeader_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:12:41.195976+00:00
-- url     : https://prove2.me/submissions/c80d8bb1-6f7d-4e6a-bc29-ff8acdb7d83e

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

open BitcoinBlockV2 in
theorem solution (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ↔
      BitcoinBlockV2.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitcoinHeader.contextualCheck ⟨h.version, (h.time : Int), BitVec.ofNat 32 h.bits⟩ S.tipHeight
        (S.timesTo S.tipHeight) S.requiredBits now = true := by
  have e1 : BitcoinHeader.medianTimePast (S.timesTo S.tipHeight) = S.mtp := rfl
  have e2 : BitcoinHeader.MAX_FUTURE_BLOCK_TIME = MAX_FUTURE_BLOCK_TIME := rfl
  unfold acceptHeader BitcoinHeader.contextualCheck
  simp only [e1, e2]
  by_cases h1 : checkHeaderPow h = true
  · by_cases h2 : h.prevBlock = S.tipHash
    · by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits
      · by_cases h4 : (h.time : Int) ≤ S.mtp
        · simp [h1, h2, h3, h4]; intros; omega
        · by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)
          · simp [h1, h2, h3, h4, h5]; intros; omega
          · by_cases hv : BitcoinHeader.versionOutdated h.version S.tipHeight = true
            · simp [h1, h2, h3, h4, h5, hv]
            · simp [h1, h2, h3, h4, h5, hv]; omega
      · simp [h1, h2, h3]
    · simp [h1, h2]
  · simp [h1]

