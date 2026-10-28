-- Prove2me | solution 2 for BitcoinSig.parseScript_p2pkh
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:21.633008+00:00
-- url     : https://prove2.me/submissions/5e228156-a5f5-43a7-82f2-699bce898de9

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

/-- Parsing the P2PKH output script bytes yields the interpreter's `p2pkhScript`. -/
theorem solution (h : Bytes) (hh : h.length = 20) :
    BitcoinSig.parseScript (BitcoinSig.p2pkhBytes h) = some (BitcoinScript.p2pkhScript h) := by
  have hp : pushBytes h = BitVec.ofNat 8 20 :: h := by
    unfold pushBytes; rw [if_pos (by rw [hh]; decide)]; rw [hh]
  unfold parseScript p2pkhBytes
  rw [hp]
  have hl : ([0x76, 0xa9] ++ (BitVec.ofNat 8 20 :: h) ++ [0x88, 0xac]).length = 25 := by simp [hh]
  rw [hl]
  have ht : (h ++ [0x88, 0xac]).take 20 = h := List.take_left' hh
  have hd : (h ++ [0x88, 0xac]).drop 20 = [0x88, 0xac] := List.drop_left' hh
  simp [parseScriptAux, getOp, OP_PUSHDATA1, OP_PUSHDATA4, ht, hd, hh, BitcoinScript.p2pkhScript]
  decide
