-- Prove2me | solution 2 for BitcoinSig.checkSig_dersig
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:20.171832+00:00
-- url     : https://prove2.me/submissions/ac56e7f3-c167-46b9-b8cf-01990844e4f4

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

/-- With `DERSIG` a non-empty signature that is not strict DER fails the script. -/
theorem solution (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode sig pk : Bytes) (hf : f.dersig = true) (hne : sig ≠ [])
    (hder : BitcoinSig.isValidSignatureEncoding sig = false) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode sig pk = none := by
  unfold checkSigPreTapscript
  have : checkSignatureEncoding f sig = false := by
    unfold checkSignatureEncoding
    rw [if_neg (by simpa using hne)]
    simp [hf, hder]
  simp [this]
