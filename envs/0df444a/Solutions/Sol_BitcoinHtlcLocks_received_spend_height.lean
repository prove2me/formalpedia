-- Prove2me | solution 1 for BitcoinHtlcLocks.received_spend_height
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:21:37.415209+00:00
-- url     : https://prove2.me/submissions/bedff624-5e17-4b7b-9a29-71a786281cf2

import Definitions.Def_BitcoinHtlcLocks
import Theorems.Thm_BitcoinHtlc_received_p2wsh_spend
import Theorems.Thm_BitcoinHtlc_cltv_concrete
import Theorems.Thm_BitcoinHtlc_checkLockTime_iff
import Theorems.Thm_BitcoinHtlcLocks_isFinalTx_height

open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

/-- **A received HTLC cannot be timed out before its expiry, at the consensus level.** A transaction
that spends a received HTLC output (pay-to-witness-script-hash of `receivedBytes`) with a
two-element witness `[sig, pk]`, under the `WITNESS` and `CHECKLOCKTIMEVERIFY` flags, and that is
final in a block at height `h`, is either a revocation spend or has `cltv_expiry < h`. -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcltv : c.flags.cltv = true)
    (revHash remoteKey localKey payHash : BitcoinSer.Bytes) (expiry : Int) (sig pk : BitcoinSer.Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hexp : 0 < expiry ∧ expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (hnIn : c.nIn < c.tx.vin.length)
    (hv : BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry)))
        ([sig, pk] ++ [BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry]) = true)
    (height : Nat) (blockTime : Int) (hfinal : BitcoinBlockV2.isFinalTx c.tx height blockTime = true) :
    BitcoinHtlcLocks.RevocationSpend c (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry) revHash pk sig ∨
      expiry < height := by
  have hd : expiry.natAbs < 2 ^ 32 := by
    have : expiry < 500000000 := by simpa [BitcoinBlockV2.LOCKTIME_THRESHOLD] using hexp.2
    omega
  obtain ⟨-, -, hsp⟩ := (BitcoinHtlc.received_p2wsh_spend tap c hf revHash remoteKey localKey payHash expiry [sig, pk]
    hrev hrem hloc hpay hd).1 hv
  have hrev' : ([sig, pk] : List BitcoinSer.Bytes).reverse = [pk, sig] := rfl
  rw [hrev'] at hsp
  unfold BitcoinHtlc.ReceivedSpend at hsp
  rcases hsp with ⟨pk', sig', heq, hh, hcs⟩ | ⟨pre, l, r, d, heq, -⟩ | ⟨x, sig', heq, -, -, hcltvp, -⟩
  · left
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨hh, hcs⟩
  · cases heq
  · right
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hcltv' : (BitcoinVerify.scriptFlagsOf c.flags).cltv = true := by simp [BitcoinVerify.scriptFlagsOf, hcltv]
    have hclt := (BitcoinHtlc.cltv_concrete (BitcoinVerify.scriptFlagsOf c.flags) (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
      (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry) expiry hcltv' (by omega)).1 hcltvp
    obtain ⟨hT, hle, hseq⟩ := (BitcoinHtlc.checkLockTime_iff c.tx c.nIn expiry (by omega) (by simpa [BitcoinBlockV2.LOCKTIME_THRESHOLD] using hexp.2)).1 hclt
    have hl : HeightLocked c.tx := ⟨by omega, by simpa [BitcoinBlockV2.LOCKTIME_THRESHOLD] using hT⟩
    have := (BitcoinHtlcLocks.isFinalTx_height c.tx height blockTime hl c.nIn hnIn
      (by simpa [BitcoinToLocal.inputSequence, BitcoinBlockV2.SEQUENCE_FINAL] using hseq)).1 hfinal
    omega
