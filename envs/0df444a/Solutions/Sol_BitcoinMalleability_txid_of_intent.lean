-- Prove2me | solution 1 for BitcoinMalleability.txid_of_intent
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T00:10:18.88055+00:00
-- url     : https://prove2.me/submissions/402e3db5-5097-491e-9f18-06123de911a1

import Definitions.Def_BitcoinMalleability
import Theorems.Thm_BitcoinVerify_native_witness_malleated
import Theorems.Thm_BitcoinSer_txid_strip
import Theorems.Thm_BitcoinMalleability_native_scriptSig_empty

open BitcoinMalleability BitcoinSer BitcoinBlockV2

private theorem stripWitness_eq_ofIntent (tx : BitcoinSer.Tx) (h : ∀ i ∈ tx.vin, i.scriptSig = []) :
    tx.stripWitness = ofIntent (intentOf tx) := by
  simp only [BitcoinSer.Tx.stripWitness, ofIntent, intentOf, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := h i hi
  cases i; simp_all

/-- For a transaction whose inputs all spend native witness programs and whose scripts verify, the
txid is the txid of the canonical transaction of its intent: no signature data enters it. -/
theorem solution (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : BitcoinSer.Tx)
    (hf : f.witness = true) (h : BitcoinBlockV2.inputScriptsOk f u tx = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid (BitcoinMalleability.ofIntent (BitcoinMalleability.intentOf tx)) := by
  rw [BitcoinSer.txid_strip tx]
  rw [stripWitness_eq_ofIntent tx (fun i hi => BitcoinMalleability.native_scriptSig_empty f u tx hf h i hi (hw i hi))]
