-- Prove2me | solution 1 for BitcoinMalleability.txid_determined
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T00:11:16.658115+00:00
-- url     : https://prove2.me/submissions/df59ffcb-350b-469a-8b16-4d762adee8d7

import Definitions.Def_BitcoinMalleability
import Theorems.Thm_BitcoinVerify_native_witness_malleated
import Theorems.Thm_BitcoinSer_txid_strip
import Theorems.Thm_BitcoinMalleability_txid_of_intent

open BitcoinMalleability BitcoinSer BitcoinBlockV2

private theorem stripWitness_eq_ofIntent (tx : BitcoinSer.Tx) (h : ∀ i ∈ tx.vin, i.scriptSig = []) :
    tx.stripWitness = ofIntent (intentOf tx) := by
  simp only [BitcoinSer.Tx.stripWitness, ofIntent, intentOf, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := h i hi
  cases i; simp_all

/-- **Non-malleability.** Two transactions with the same intent, both of whose scripts verify
against the same ledger, where the inputs spend native witness programs, have the same txid: no
choice of signatures or witnesses, by the signer or by a third party, changes it. -/
theorem solution (f : BitcoinActivation.ScriptFlags) (u : Ledger)
    (tx tx' : BitcoinSer.Tx) (hf : f.witness = true)
    (hI : BitcoinMalleability.intentOf tx = BitcoinMalleability.intentOf tx')
    (h : BitcoinBlockV2.inputScriptsOk f u tx = true) (h' : BitcoinBlockV2.inputScriptsOk f u tx' = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid tx' := by
  have hw' : SpendsWitnessPrograms u tx' := by
    intro i' hi'
    have hmap : tx.vin.map (fun i => (i.prevout, i.nSequence)) = tx'.vin.map (fun i => (i.prevout, i.nSequence)) := by
      have := congrArg Intent.inputs hI; simpa [intentOf] using this
    have hm : (i'.prevout, i'.nSequence) ∈ tx.vin.map (fun i => (i.prevout, i.nSequence)) := by
      rw [hmap]; exact List.mem_map_of_mem hi'
    obtain ⟨i, hi, heq⟩ := List.mem_map.1 hm
    have hp : i.prevout = i'.prevout := (Prod.mk.inj heq).1
    rw [← hp]; exact hw i hi
  rw [BitcoinMalleability.txid_of_intent f u tx hf h hw, BitcoinMalleability.txid_of_intent f u tx' hf h' hw', hI]
