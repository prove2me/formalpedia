-- Prove2me | solution 1 for BitcoinHtlcLocks.presigned_timeout_height
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:21:36.360537+00:00
-- url     : https://prove2.me/submissions/90503c47-565f-4ccd-8d6b-839555a473cf

import Definitions.Def_BitcoinHtlcLocks
import Theorems.Thm_BitcoinHtlc_received_p2wsh_spend
import Theorems.Thm_BitcoinHtlc_cltv_concrete
import Theorems.Thm_BitcoinHtlc_checkLockTime_iff
import Theorems.Thm_BitcoinHtlcLocks_isFinalTx_height

open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

/-- A pre-signed HTLC-timeout transaction (lock time = the expiry, a block height; the HTLC input
not final) is accepted in a block only above the expiry height. -/
theorem solution (tx : BitcoinSer.Tx) (expiry height : Nat) (blockTime : Int)
    (hexp : 0 < expiry ∧ expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (htx : tx.nLockTime = expiry)
    (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL)
    (hfinal : BitcoinBlockV2.isFinalTx tx height blockTime = true) : expiry < height := by
  have := (BitcoinHtlcLocks.isFinalTx_height tx height blockTime ⟨by omega, by omega⟩ i hi hseq).1 hfinal
  omega
