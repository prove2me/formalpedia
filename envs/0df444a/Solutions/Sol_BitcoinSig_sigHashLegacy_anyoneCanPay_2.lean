-- Prove2me | solution 2 for BitcoinSig.sigHashLegacy_anyoneCanPay
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:15.849786+00:00
-- url     : https://prove2.me/submissions/139e42c2-9131-4b28-a5c0-41b433ce250b

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

/-- With `SIGHASH_ANYONECANPAY` the legacy hash depends on the signed input alone (plus version,
outputs and lock time). -/
theorem solution (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (hacp : hashType &&& BitcoinSig.SIGHASH_ANYONECANPAY ≠ 0)
    (h1 : tx'.version = tx.version) (h2 : tx'.vout = tx.vout) (h3 : tx'.nLockTime = tx.nLockTime)
    (h4 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout)
    (h5 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence) :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by
  have hs : serSigTx tx' scriptCode nIn hashType = serSigTx tx scriptCode nIn hashType := by
    have ho : serSigOutput tx' nIn = serSigOutput tx nIn := by
      funext s k; simp [serSigOutput, h2]
    have hi : ∀ s z, serSigInput tx' scriptCode nIn true s z 0 = serSigInput tx scriptCode nIn true s z 0 := by
      intro s z; unfold serSigInput; dsimp only; simp only [ite_true]; rw [h4, h5]
    unfold serSigTx
    dsimp only
    have hd : decide (hashType &&& SIGHASH_ANYONECANPAY ≠ 0) = true := decide_eq_true hacp
    rw [h1, h2, h3, ho, hd]
    simp only [ite_true, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, hi]
  unfold sigHashLegacy
  rw [h2, hs]
