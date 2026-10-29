-- Prove2me | solution 1 for BitcoinMalleability.p2sh_wrapped_scriptSig
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T00:09:32.293727+00:00
-- url     : https://prove2.me/submissions/5c3adcb1-7448-43b5-aaf1-d478be403c1a

import Definitions.Def_BitcoinMalleability
import Theorems.Thm_BitcoinVerify_native_witness_malleated
import Theorems.Thm_BitcoinSer_txid_strip

open BitcoinMalleability BitcoinSer BitcoinBlockV2

private theorem stripWitness_eq_ofIntent (tx : BitcoinSer.Tx) (h : ∀ i ∈ tx.vin, i.scriptSig = []) :
    tx.stripWitness = ofIntent (intentOf tx) := by
  simp only [BitcoinSer.Tx.stripWitness, ofIntent, intentOf, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := h i hi
  cases i; simp_all

private theorem isWitnessProgram_p2sh (spk : BitcoinSer.Bytes) (h : BitcoinVerify.isPayToScriptHash spk = true) :
    BitcoinVerify.isWitnessProgram spk = none := by
  simp only [BitcoinVerify.isPayToScriptHash, Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 : (spk.getD 0 0).toNat = 169 := h.1.1.2
  simp only [BitcoinVerify.isWitnessProgram, h.1.1.1, h0]
  rw [if_neg (by omega), if_pos (by omega)]

/-- A P2SH output spent with witness data: `VerifyScript` succeeds only if the `scriptSig` is
exactly the push of the redeem script it evaluates to, and that redeem script is a witness program
(`SCRIPT_ERR_WITNESS_MALLEATED_P2SH`). -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (sig spk : BitcoinSer.Bytes) (w : List BitcoinSer.Bytes) (hp : c.flags.p2sh = true) (hf : c.flags.witness = true)
    (hspk : BitcoinVerify.isPayToScriptHash spk = true) (hw : w ≠ [])
    (hv : BitcoinVerify.verifyScript tap c sig spk w = true) :
    ∃ redeem rest, BitcoinVerify.evalBytes c .base [] sig = some (redeem :: rest) ∧
      BitcoinVerify.isWitnessProgram redeem ≠ none ∧ sig = BitcoinSig.pushBytes redeem := by
  have hnw := isWitnessProgram_p2sh spk hspk
  unfold BitcoinVerify.verifyScript at hv
  cases hsig : BitcoinVerify.evalBytes c .base [] sig with
  | none => simp only [hsig] at hv; cases hv
  | some stackSig =>
    simp only [hsig] at hv
    cases hspk' : BitcoinVerify.evalBytes c .base stackSig spk with
    | none => simp only [hspk'] at hv; cases hv
    | some stack =>
      simp only [hspk'] at hv
      simp only [hf, hnw, hp, hspk, Bool.true_and, ite_true] at hv
      by_cases ht : BitcoinVerify.topTrue stack = true
      · simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false] at hv
        by_cases hpo : BitcoinVerify.isPushOnly sig = true
        · simp only [hpo, Bool.not_true, Bool.false_eq_true, ite_false] at hv
          cases stackSig with
          | nil => cases hv
          | cons redeem rest =>
            refine ⟨redeem, rest, rfl, ?_⟩
            dsimp only at hv
            cases hev : BitcoinVerify.evalBytes c .base rest redeem with
            | none => simp only [hev] at hv; cases hv
            | some st2 =>
              simp only [hev] at hv
              by_cases ht2 : BitcoinVerify.topTrue st2 = true
              · simp only [ht2, Bool.not_true, Bool.false_eq_true, ite_false] at hv
                cases hwr : BitcoinVerify.isWitnessProgram redeem with
                | none =>
                  simp only [hwr] at hv
                  have : w.isEmpty = true := by
                    cases hemp : w.isEmpty
                    · simp [hemp, hf] at hv
                    · rfl
                  exact absurd (List.isEmpty_iff.1 this) hw
                | some vp =>
                  simp only [hwr] at hv
                  refine ⟨by simp, ?_⟩
                  by_cases hne : sig = BitcoinSig.pushBytes redeem
                  · exact hne
                  · simp [hne] at hv
              · simp [ht2] at hv
        · simp [hpo] at hv
      · simp [ht] at hv
