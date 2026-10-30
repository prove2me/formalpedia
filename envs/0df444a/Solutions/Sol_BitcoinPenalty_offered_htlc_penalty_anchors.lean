-- Prove2me | solution 1 for BitcoinPenalty.offered_htlc_penalty_anchors
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:31:36.226004+00:00
-- url     : https://prove2.me/submissions/e9dd2929-0454-400f-8fd4-430b17ddd73e

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

/-- **Offered-HTLC penalty with `option_anchors`.** The revocation path skips the
`1 OP_CHECKSEQUENCEVERIFY` suffix, so no delay applies. -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.offeredBytesAnchors K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytesAnchors K h)) = true := by
  obtain ⟨⟨sigR, hlen, hsig⟩, hrev⟩ := hR
  refine ⟨sigR, ?_⟩
  simp only [BitcoinPenalty.htlcPenaltyWitness, BitcoinPenalty.p2wshOf, BitcoinPenalty.offeredBytesAnchors,
    BitcoinPenalty.oracleOf] at hh hsig hrev ⊢
  exact (BitcoinAnchors.offered_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash [sigR, K.revPk]
    hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash).2
    ⟨hh, mem_two_le sigR K.revPk hlen hK.revPk, Or.inl ⟨K.revPk, sigR, reverse_two sigR K.revPk, hrev, hsig⟩⟩
