-- Prove2me | solution 1 for BitcoinPenalty.revoked_commitment_penalty
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:33:06.796258+00:00
-- url     : https://prove2.me/submissions/141e69b4-67b7-478f-add8-ed1e6bcd596c

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
import Theorems.Thm_BitcoinPenalty_offered_htlc_penalty
import Theorems.Thm_BitcoinPenalty_offered_htlc_penalty_anchors
import Theorems.Thm_BitcoinPenalty_received_htlc_penalty
import Theorems.Thm_BitcoinPenalty_received_htlc_penalty_anchors
import Theorems.Thm_BitcoinPenalty_to_local_penalty

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

/-- **A whole revoked commitment, one context.** If in the spending context `c` the honest party
has an accepted revocation signature for every witness script (`∀ sc, HoldsRevocation (oracleOf c sc) K`),
then `to_local`, the offered and received HTLC outputs (both forms) all have an accepted penalty
witness. -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hR : ∀ sc, BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c sc) K)
    (hh : ∀ sc ∈ [BitcoinPenalty.toLocalBytes K, BitcoinPenalty.offeredBytes K h, BitcoinPenalty.receivedBytes K h,
        BitcoinPenalty.offeredBytesAnchors K h, BitcoinPenalty.receivedBytesAnchors K h],
      BitcoinScript.castToBool (BitcoinSer.sha256 sc) = true) :
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
        (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytesAnchors K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytesAnchors K h)) = true) := by
  refine ⟨BitcoinPenalty.to_local_penalty tap c hf K hK (hh _ (by simp)) (hR _),
    BitcoinPenalty.offered_htlc_penalty tap c hf K hK h hw (hh _ (by simp)) (hR _),
    BitcoinPenalty.received_htlc_penalty tap c hf K hK h hw (hh _ (by simp)) (hR _),
    BitcoinPenalty.offered_htlc_penalty_anchors tap c hf K hK h hw (hh _ (by simp)) (hR _),
    BitcoinPenalty.received_htlc_penalty_anchors tap c hf K hK h hw (hh _ (by simp)) (hR _)⟩
