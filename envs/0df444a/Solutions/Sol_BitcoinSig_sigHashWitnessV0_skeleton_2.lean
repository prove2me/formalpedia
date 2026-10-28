-- Prove2me | solution 2 for BitcoinSig.sigHashWitnessV0_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:16.586448+00:00
-- url     : https://prove2.me/submissions/ff46236c-1911-4044-904f-f742ce352332

import Definitions.Def_BitcoinSig
import Theorems.Thm_BitcoinScript_p2pkh_correct

open BitcoinSig BitcoinSer

private def skel (i : TxIn) : OutPoint × Nat := (i.prevout, i.nSequence)

private def dflt : TxIn := ⟨⟨[], 0⟩, [], 0, []⟩

private theorem getD_prevout (vin : List TxIn) (k : Nat) :
    (vin.getD k dflt).prevout = ((vin.map skel).getD k (skel dflt)).1 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vin[k]? <;> rfl

private theorem getD_seq (vin : List TxIn) (k : Nat) :
    (vin.getD k dflt).nSequence = ((vin.map skel).getD k (skel dflt)).2 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vin[k]? <;> rfl

private theorem skel_getD (vin vin' : List TxIn) (hv : vin'.map skel = vin.map skel) (j : Nat) :
    (vin'.getD j dflt).prevout = (vin.getD j dflt).prevout ∧
    (vin'.getD j dflt).nSequence = (vin.getD j dflt).nSequence := by
  constructor
  · rw [getD_prevout, getD_prevout, hv]
  · rw [getD_seq, getD_seq, hv]

private theorem serSigInput_skel (tx tx' : Tx) (h : BitcoinSig.sameSkeleton tx tx') (sc : Bytes) (nIn : Nat)
    (a s z : Bool) :
    serSigInput tx' sc nIn a s z = serSigInput tx sc nIn a s z := by
  obtain ⟨_, _, _, hv⟩ := h
  have hv' : tx'.vin.map skel = tx.vin.map skel := hv
  funext k
  unfold serSigInput
  have e := skel_getD tx.vin tx'.vin hv'
  simp only [show (⟨⟨[], 0⟩, [], 0, []⟩ : TxIn) = dflt from rfl, (e _).1, (e _).2]

private theorem serSigTx_skel (tx tx' : Tx) (h : BitcoinSig.sameSkeleton tx tx') (sc : Bytes) (nIn ht : Nat) :
    serSigTx tx' sc nIn ht = serSigTx tx sc nIn ht := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen : tx'.vin.length = tx.vin.length := by
    have := congrArg List.length h4; simpa using this
  have ho : serSigOutput tx' nIn = serSigOutput tx nIn := by
    funext s k; simp [serSigOutput, h2]
  unfold serSigTx
  dsimp only
  rw [h1, h2, h3, hlen, serSigInput_skel tx tx' ⟨h1, h2, h3, h4⟩, ho]

/-- The BIP143 hash never depends on scriptSigs or witnesses either. -/
theorem solution (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat) (amount : Int)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashWitnessV0 scriptCode tx' nIn hashType amount =
      BitcoinSig.sigHashWitnessV0 scriptCode tx nIn hashType amount := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : tx'.vin.flatMap (fun i => serOutPoint i.prevout) = tx.vin.flatMap (fun i => serOutPoint i.prevout) := by
    have := congrArg (fun l => l.flatMap (fun q : OutPoint × Nat => serOutPoint q.1)) h4
    simpa [List.flatMap_map] using this
  have e2 : tx'.vin.flatMap (fun i => ser32 i.nSequence) = tx.vin.flatMap (fun i => ser32 i.nSequence) := by
    have := congrArg (fun l => l.flatMap (fun q : OutPoint × Nat => ser32 q.2)) h4
    simpa [List.flatMap_map] using this
  have e := skel_getD tx.vin tx'.vin h4 nIn
  unfold sigHashWitnessV0
  simp only [h1, h2, h3, e1, e2, show (⟨⟨[], 0⟩, [], 0, []⟩ : TxIn) = dflt from rfl, e.1, e.2]
