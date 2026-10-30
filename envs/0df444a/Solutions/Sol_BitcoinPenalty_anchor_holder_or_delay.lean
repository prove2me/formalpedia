-- Prove2me | solution 1 for BitcoinPenalty.anchor_holder_or_delay
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:31:38.616025+00:00
-- url     : https://prove2.me/submissions/81614f71-4a78-4a6e-a79e-fdc2ada468ba

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

/-- **Anchors: the key holder at once, anyone after 16 blocks.** Each anchor (keyed by one side's
funding key) is spendable exactly by a lone element that is either an accepted signature for that
key, or a cleanly rejected one (such as the empty signature) with the 16-block delay check passing. -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (fk : BitcoinSer.Bytes) (hfk : fk = K.fundingKeyLocal ∨ fk = K.fundingKeyRemote) (ws : List BitcoinSer.Bytes) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinAnchors.anchorBytes fk))
        (ws ++ [BitcoinAnchors.anchorBytes fk]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fk)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      ∃ sig, ws = [sig] ∧
        ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some true ∨
          ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some false ∧
            BitcoinToLocal.CsvPasses (BitcoinVerify.scriptFlagsOf c.flags)
              (BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)) 16)) := by
  have hlen : fk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE := by
    rcases hfk with rfl | rfl
    · exact hK.fundingKeyLocal
    · exact hK.fundingKeyRemote
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.oracleOf]
  rw [BitcoinAnchors.anchor_p2wsh_spend tap c hf fk ws hlen]
  unfold BitcoinAnchors.AnchorSpend
  constructor
  · rintro ⟨h1, h2, sig, hws, h3⟩
    refine ⟨h1, h2, sig, ?_, h3⟩
    have := congrArg List.reverse hws
    simpa using this
  · rintro ⟨h1, h2, sig, hws, h3⟩
    subst hws
    exact ⟨h1, h2, sig, rfl, h3⟩
