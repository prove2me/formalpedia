-- Prove2me | solution 2 for BitcoinSig.derEncode_valid
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:22.414252+00:00
-- url     : https://prove2.me/submissions/1fc2b456-8c99-443b-97e0-d38968556d13

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

/-- The DER layout encodes validly whenever both integers are minimal and the total fits. -/
theorem solution (r s : Bytes) (ht : Byte) (hr : BitcoinSig.minimalInt r)
    (hs : BitcoinSig.minimalInt s) (hlen : r.length + s.length ≤ 66) :
    BitcoinSig.isValidSignatureEncoding (BitcoinSig.derEncode r s ht) = true := by
  obtain ⟨hr0, hr1, hr2⟩ := hr
  obtain ⟨hs0, hs1, hs2⟩ := hs
  have hrl : 1 ≤ r.length := List.length_pos_iff.2 hr0
  have hsl : 1 ≤ s.length := List.length_pos_iff.2 hs0
  -- the layout, right-associated
  have hsig : derEncode r s ht =
      [0x30, BitVec.ofNat 8 (r.length + s.length + 4), 0x02, BitVec.ofNat 8 r.length] ++
        (r ++ ([0x02, BitVec.ofNat 8 s.length] ++ (s ++ [ht]))) := by
    simp [derEncode]
  rw [hsig]
  generalize hE : ([0x30, BitVec.ofNat 8 (r.length + s.length + 4), 0x02, BitVec.ofNat 8 r.length] ++
        (r ++ ([0x02, BitVec.ofNat 8 s.length] ++ (s ++ [ht]))) : Bytes) = sig
  have hL : sig.length = r.length + s.length + 7 := by rw [← hE]; simp; omega
  have hb3 : (sig.getD 3 0).toNat = r.length := by
    rw [← hE, getD_app_lt _ _ _ _ (by simp)]; simp [BitVec.toNat_ofNat] <;> omega
  have hb1 : (sig.getD 1 0).toNat = r.length + s.length + 4 := by
    rw [← hE, getD_app_lt _ _ _ _ (by simp)]; simp [BitVec.toNat_ofNat] <;> omega
  have hb0 : (sig.getD 0 0).toNat = 0x30 := by rw [← hE, getD_app_lt _ _ _ _ (by simp)]; rfl
  have hb2 : (sig.getD 2 0).toNat = 0x02 := by rw [← hE, getD_app_lt _ _ _ _ (by simp)]; rfl
  have hb4 : (sig.getD 4 0).toNat = (r.getD 0 0).toNat := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp), getD_app_lt _ _ _ _ (by simp <;> omega)]; rfl
  have hb5 : 1 < r.length → (sig.getD 5 0).toNat = (r.getD 1 0).toNat := by
    intro h
    rw [← hE, getD_app_ge _ _ _ _ (by simp), getD_app_lt _ _ _ _ (by simp <;> omega)]; rfl
  have hR4 : (sig.getD (r.length + 4) 0).toNat = 0x02 := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega)]
    simp
  have hR5 : (sig.getD (5 + r.length) 0).toNat = s.length := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show 5 + r.length - 4 - r.length = 1 by omega]
    simp [BitVec.toNat_ofNat] <;> omega
  have hR6 : (sig.getD (r.length + 6) 0).toNat = (s.getD 0 0).toNat := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega),
      getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_lt _ _ _ _ (by simp <;> omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show r.length + 6 - 4 - r.length - 2 = 0 by omega]
  have hR7 : 1 < s.length → (sig.getD (r.length + 7) 0).toNat = (s.getD 1 0).toNat := by
    intro h
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega),
      getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_lt _ _ _ _ (by simp <;> omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show r.length + 7 - 4 - r.length - 2 = 1 by omega]
  unfold isValidSignatureEncoding
  dsimp only
  simp only [hL, hb0, hb1, hb2, hb3, hb4, hR4, hR5, hR6]
  repeat' (first
    | rw [if_neg (by omega)]
    | rw [if_neg (by rintro ⟨h1, h2, h3⟩; rw [hb5 h1] at h3; have := hr2 h1 h2; omega)]
    | rw [if_neg (by rintro ⟨h1, h2, h3⟩; rw [hR7 h1] at h3; have := hs2 h1 h2; omega)])
