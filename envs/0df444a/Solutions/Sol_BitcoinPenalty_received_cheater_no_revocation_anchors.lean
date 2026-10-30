-- Prove2me | solution 1 for BitcoinPenalty.received_cheater_no_revocation_anchors
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:31:42.793992+00:00
-- url     : https://prove2.me/submissions/9b4ed84c-2340-4d8c-aa32-f25968297396

import Definitions.Def_BitcoinPenalty
import Theorems.Thm_BitcoinToLocal_p2wsh_spend
import Theorems.Thm_BitcoinToLocal_csv_concrete
import Theorems.Thm_BitcoinToLocal_lightning_delay
import Theorems.Thm_BitcoinToLocal_checkSequence_iff
import Theorems.Thm_BitcoinHtlc_offered_p2wsh_spend
import Theorems.Thm_BitcoinHtlc_received_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_offered_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_received_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_to_remote_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_anchor_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_anchor_anyone_delay
import Theorems.Thm_BitcoinHtlcLocks_received_spend_height

open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

private theorem delay_natAbs (K : CommitmentKeys) (hK : WellFormed K) : K.toSelfDelay.natAbs < 2 ^ 32 := by
  have := hK.delayNonneg; have := hK.delayLt; omega

private theorem reverse_two (a b : BitcoinSer.Bytes) : [a, b].reverse = [b, a] := by simp

private theorem mem_two_le (a b : BitcoinSer.Bytes) (ha : a.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hb : b.length ≤ MAX_SCRIPT_ELEMENT_SIZE) : ∀ e ∈ [a, b], e.length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact ha
  · exact hb

/-- A passing `OP_CHECKSEQUENCEVERIFY` under the concrete oracle, in transaction terms: version at
least 2, the disable bit clear, and `nSequence` at least the operand. -/
private theorem csv_tx (c : Ctx) (sc : BitcoinSer.Bytes) (delay : Int) (hcsv : c.flags.csv = true)
    (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16)
    (h : CsvPasses (scriptFlagsOf c.flags) (oracleOf c sc) delay) :
    2 ≤ c.tx.version ∧ inputSequence c.tx c.nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      delay.toNat ≤ inputSequence c.tx c.nIn := by
  have hcs : checkSequence c.tx c.nIn delay = true :=
    (BitcoinToLocal.csv_concrete (scriptFlagsOf c.flags) (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 sc delay
      hcsv h0 h16).1 h
  have := (BitcoinToLocal.checkSequence_iff c.tx c.nIn delay h0 h16).1 hcs
  exact ⟨this.1, this.2.1, Nat.le_trans this.2.2.2 Nat.and_le_left⟩

/-- **Received HTLC with `option_anchors`: the cheater never takes the revocation path**, and the
one-block delay check applies to whatever path it takes. -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
      (ws ++ [BitcoinPenalty.receivedBytesAnchors K h]) = true) :
    BitcoinPenalty.ReceivedNonRevocationAnchors (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K h ws.reverse := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.receivedBytesAnchors, BitcoinPenalty.oracleOf,
    BitcoinPenalty.NoRevocationSig, BitcoinPenalty.NoRevHashPreimage, BitcoinPenalty.ReceivedNonRevocationAnchors,
    BitcoinPenalty.ReceivedNonRevocation] at hN hP hv ⊢
  obtain ⟨_, _, hsp⟩ := (BitcoinAnchors.received_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash
    h.expiry ws hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash hw.expiry).1 hv
  rcases hsp with ⟨pk, sig, _, hpk, hsig⟩ | ⟨preimage, localSig, remoteSig, dummy, hws, h1, h2, h3, h4, h5, h6⟩ |
    ⟨x, sig, hws, h1, h2, h3, h4, h5⟩
  · have := hP pk hpk
    subst this
    exact absurd hsig (hN sig)
  · exact ⟨Or.inl ⟨preimage, localSig, remoteSig, dummy, hws, h1, h2, h3, h4, h5⟩, h6⟩
  · exact ⟨Or.inr ⟨x, sig, hws, h1, h2, h3, h4⟩, h5⟩
