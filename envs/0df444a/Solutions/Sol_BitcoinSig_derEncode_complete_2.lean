-- Prove2me | solution 2 for BitcoinSig.derEncode_complete
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:23.131301+00:00
-- url     : https://prove2.me/submissions/da65c400-1ef5-4a75-ae73-75468244b104

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

/-- Every signature `IsValidSignatureEncoding` accepts has the DER layout with minimal integers:
the three leading-zero rules are exactly what forces the layout. -/
theorem solution (sig : Bytes) (h : BitcoinSig.isValidSignatureEncoding sig = true) :
    ∃ (r s : Bytes) (ht : Byte), sig = BitcoinSig.derEncode r s ht ∧ BitcoinSig.minimalInt r ∧
      BitcoinSig.minimalInt s ∧ r.length + s.length ≤ 66 := by
  unfold isValidSignatureEncoding at h
  dsimp only at h
  -- peel the fourteen tests
  by_cases c1 : sig.length < 9
  · rw [if_pos c1] at h; cases h
  rw [if_neg c1] at h
  by_cases c2 : 73 < sig.length
  · rw [if_pos c2] at h; cases h
  rw [if_neg c2] at h
  by_cases c3 : (sig.getD 0 0).toNat ≠ 0x30
  · rw [if_pos c3] at h; cases h
  rw [if_neg c3] at h
  by_cases c4 : (sig.getD 1 0).toNat ≠ sig.length - 3
  · rw [if_pos c4] at h; cases h
  rw [if_neg c4] at h
  by_cases c5 : sig.length ≤ 5 + (sig.getD 3 0).toNat
  · rw [if_pos c5] at h; cases h
  rw [if_neg c5] at h
  by_cases c6 : (sig.getD 3 0).toNat + (sig.getD (5 + (sig.getD 3 0).toNat) 0).toNat + 7 ≠ sig.length
  · rw [if_pos c6] at h; cases h
  rw [if_neg c6] at h
  by_cases c7 : (sig.getD 2 0).toNat ≠ 0x02
  · rw [if_pos c7] at h; cases h
  rw [if_neg c7] at h
  by_cases c8 : (sig.getD 3 0).toNat = 0
  · rw [if_pos c8] at h; cases h
  rw [if_neg c8] at h
  by_cases c9 : 0x80 ≤ (sig.getD 4 0).toNat
  · rw [if_pos c9] at h; cases h
  rw [if_neg c9] at h
  by_cases c10 : 1 < (sig.getD 3 0).toNat ∧ (sig.getD 4 0).toNat = 0 ∧ (sig.getD 5 0).toNat < 0x80
  · rw [if_pos c10] at h; cases h
  rw [if_neg c10] at h
  by_cases c11 : (sig.getD ((sig.getD 3 0).toNat + 4) 0).toNat ≠ 0x02
  · rw [if_pos c11] at h; cases h
  rw [if_neg c11] at h
  by_cases c12 : (sig.getD (5 + (sig.getD 3 0).toNat) 0).toNat = 0
  · rw [if_pos c12] at h; cases h
  rw [if_neg c12] at h
  by_cases c13 : 0x80 ≤ (sig.getD ((sig.getD 3 0).toNat + 6) 0).toNat
  · rw [if_pos c13] at h; cases h
  rw [if_neg c13] at h
  by_cases c14 : 1 < (sig.getD (5 + (sig.getD 3 0).toNat) 0).toNat ∧ (sig.getD ((sig.getD 3 0).toNat + 6) 0).toNat = 0 ∧
      (sig.getD ((sig.getD 3 0).toNat + 7) 0).toNat < 0x80
  · rw [if_pos c14] at h; cases h
  clear h
  -- name the pieces
  generalize hlR : (sig.getD 3 0).toNat = lenR at *
  generalize hlS : (sig.getD (5 + lenR) 0).toNat = lenS at *
  have hlen : sig.length = lenR + lenS + 7 := by omega
  refine ⟨(sig.drop 4).take lenR, (sig.drop (6 + lenR)).take lenS, sig.getD (lenR + lenS + 6) 0, ?_, ?_, ?_, ?_⟩
  · -- the layout: cut `sig` at 4, 4 + lenR, 6 + lenR, 6 + lenR + lenS
    have e1 : sig = sig.take 4 ++ sig.drop 4 := (List.take_append_drop 4 sig).symm
    have e2 : sig.drop 4 = (sig.drop 4).take lenR ++ (sig.drop 4).drop lenR := (List.take_append_drop _ _).symm
    have e3 : (sig.drop 4).drop lenR = sig.drop (4 + lenR) := by rw [List.drop_drop]
    have e4 : sig.drop (4 + lenR) = (sig.drop (4 + lenR)).take 2 ++ (sig.drop (4 + lenR)).drop 2 := (List.take_append_drop _ _).symm
    have e5 : (sig.drop (4 + lenR)).drop 2 = sig.drop (6 + lenR) := by rw [List.drop_drop]; congr 1; omega
    have e6 : sig.drop (6 + lenR) = (sig.drop (6 + lenR)).take lenS ++ (sig.drop (6 + lenR)).drop lenS := (List.take_append_drop _ _).symm
    have e7 : (sig.drop (6 + lenR)).drop lenS = sig.drop (6 + lenR + lenS) := by rw [List.drop_drop]
    have e8 : sig.drop (6 + lenR + lenS) = [sig.getD (lenR + lenS + 6) 0] := by
      have := eq_single (sig.drop (6 + lenR + lenS)) (by simp; omega)
      rw [getD_drop'] at this
      rw [this]; congr 2; omega
    have t4 : sig.take 4 = [sig.getD 0 0, sig.getD 1 0, sig.getD 2 0, sig.getD 3 0] := take4_eq sig (by omega)
    have t2 : (sig.drop (4 + lenR)).take 2 = [sig.getD (4 + lenR) 0, sig.getD (4 + lenR + 1) 0] := by
      rw [take2_eq _ (by simp; omega), getD_drop', getD_drop', Nat.add_zero]
    have hr : ((sig.drop 4).take lenR).length = lenR := by simp; omega
    have hs : ((sig.drop (6 + lenR)).take lenS).length = lenS := by simp; omega
    have b0 : sig.getD 0 0 = 0x30 := by
      have := ofNat_toNat' (sig.getD 0 0); rw [show (sig.getD 0 0).toNat = 0x30 by omega] at this; exact this.symm
    have b2 : sig.getD 2 0 = 0x02 := by
      have := ofNat_toNat' (sig.getD 2 0); rw [show (sig.getD 2 0).toNat = 0x02 by omega] at this; exact this.symm
    have b1 : sig.getD 1 0 = BitVec.ofNat 8 (lenR + lenS + 4) := by
      have := ofNat_toNat' (sig.getD 1 0)
      rw [show (sig.getD 1 0).toNat = lenR + lenS + 4 by omega] at this
      exact this.symm
    have b3 : sig.getD 3 0 = BitVec.ofNat 8 lenR := by
      have := ofNat_toNat' (sig.getD 3 0)
      rw [hlR] at this
      exact this.symm
    have bR4 : sig.getD (4 + lenR) 0 = 0x02 := by
      have := ofNat_toNat' (sig.getD (4 + lenR) 0)
      rw [show 4 + lenR = lenR + 4 by omega, show (sig.getD (lenR + 4) 0).toNat = 0x02 by omega] at this
      rw [show 4 + lenR = lenR + 4 by omega]; exact this.symm
    have bR5 : sig.getD (4 + lenR + 1) 0 = BitVec.ofNat 8 lenS := by
      have := ofNat_toNat' (sig.getD (4 + lenR + 1) 0)
      rw [show 4 + lenR + 1 = 5 + lenR by omega, hlS] at this
      rw [show 4 + lenR + 1 = 5 + lenR by omega]; exact this.symm
    unfold derEncode
    rw [hr, hs]
    conv => lhs; rw [e1, t4, e2, e3, e4, t2, e5, e6, e7, e8, b0, b1, b2, b3, bR4, bR5]
    simp
  · refine ⟨?_, ?_, ?_⟩
    · intro hnil
      have := congrArg List.length hnil
      simp at this; omega
    · rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero]; omega
    · intro h1 h2
      simp only [List.length_take, List.length_drop] at h1
      rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero] at h2
      rw [getD_take' _ _ _ _ (by omega), getD_drop', show (4:Nat) + 1 = 5 from rfl]
      omega
  · refine ⟨?_, ?_, ?_⟩
    · intro hnil
      have := congrArg List.length hnil
      simp at this; omega
    · rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero, show 6 + lenR = lenR + 6 by omega]; omega
    · intro h1 h2
      simp only [List.length_take, List.length_drop] at h1
      rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero, show 6 + lenR = lenR + 6 by omega] at h2
      rw [getD_take' _ _ _ _ (by omega), getD_drop', show 6 + lenR + 1 = lenR + 7 by omega]
      omega
  · simp only [List.length_take, List.length_drop]; omega
