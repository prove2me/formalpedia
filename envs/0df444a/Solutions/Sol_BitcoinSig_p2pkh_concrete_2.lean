-- Prove2me | solution 2 for BitcoinSig.p2pkh_concrete
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:24.017526+00:00
-- url     : https://prove2.me/submissions/01e0cbe0-f86c-402a-a636-e2bb82e93c35

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

private theorem getD_app_lt {α : Type} (a b : List α) (i : Nat) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_app_ge {α : Type} (a b : List α) (i : Nat) (d : α) (h : a.length ≤ i) :
    (a ++ b).getD i d = b.getD (i - a.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem getD_drop' {α : Type} (l : List α) (k i : Nat) (d : α) : (l.drop k).getD i d = l.getD (k + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem getD_take' {α : Type} (l : List α) (k i : Nat) (d : α) (h : i < k) : (l.take k).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

private theorem take4_eq (l : Bytes) (h : 4 ≤ l.length) :
    l.take 4 = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l with
  | a :: b :: c :: d :: _ => rfl
  | [] | [_] | [_, _] | [_, _, _] => simp at h

private theorem take2_eq (l : Bytes) (h : 2 ≤ l.length) : l.take 2 = [l.getD 0 0, l.getD 1 0] := by
  match l with
  | a :: b :: _ => rfl
  | [] | [_] => simp at h

private theorem eq_single (l : Bytes) (h : l.length = 1) : l = [l.getD 0 0] := by
  match l with
  | [a] => rfl
  | [] | _ :: _ :: _ => simp at h

private theorem ofNat_toNat' (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `VerifyScript` for P2PKH with Core's hashes and signature checker: success iff the key hashes to
the committed value and the pre-tapscript signature check on the output script accepts. -/
theorem solution (f : SigFlags) (fl : BitcoinScript.Flags) (tx : Tx) (nIn : Nat) (amount : Int)
    (v : SigVersion) (sig pk h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain fl (BitcoinSig.legacyOracle f tx nIn amount v (BitcoinSig.p2pkhBytes h))
        [.push sig, .push pk] (BitcoinScript.p2pkhScript h) = true ↔
      BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript f tx nIn amount v (BitcoinSig.p2pkhBytes h) sig pk = some true :=
  BitcoinScript.p2pkh_correct fl (legacyOracle f tx nIn amount v (p2pkhBytes h)) sig pk h hsig hpk hh
