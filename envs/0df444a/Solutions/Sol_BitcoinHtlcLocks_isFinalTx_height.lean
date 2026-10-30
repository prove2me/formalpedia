-- Prove2me | solution 1 for BitcoinHtlcLocks.isFinalTx_height
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:21:09.572962+00:00
-- url     : https://prove2.me/submissions/6b79bcae-03b8-4828-a31d-2a018d385627

import Definitions.Def_BitcoinHtlcLocks
import Theorems.Thm_BitcoinHtlc_received_p2wsh_spend
import Theorems.Thm_BitcoinHtlc_cltv_concrete
import Theorems.Thm_BitcoinHtlc_checkLockTime_iff

open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

/-- `IsFinalTx` for a height-locked transaction with a non-final input: the transaction is final at
height `h` exactly when its lock time is below `h`. -/
theorem solution (tx : BitcoinSer.Tx) (height : Nat) (blockTime : Int)
    (hl : BitcoinHtlcLocks.HeightLocked tx) (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL) :
    BitcoinBlockV2.isFinalTx tx height blockTime = true ↔ tx.nLockTime < height := by
  obtain ⟨h0, hT⟩ := hl
  unfold BitcoinBlockV2.isFinalTx
  rw [if_neg (by omega), if_pos hT]
  have hall : (tx.vin.all fun i => decide (i.nSequence = BitcoinBlockV2.SEQUENCE_FINAL)) = false := by
    rw [List.all_eq_false]
    refine ⟨tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩, ?_, by simpa using hseq⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  by_cases hlt : (tx.nLockTime : Int) < (height : Int)
  · rw [if_pos hlt]; simp; omega
  · rw [if_neg hlt, hall]; simp; omega
