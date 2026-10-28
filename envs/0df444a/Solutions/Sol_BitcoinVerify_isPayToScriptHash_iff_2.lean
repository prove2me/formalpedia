-- Prove2me | solution 2 for BitcoinVerify.isPayToScriptHash_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:54.293989+00:00
-- url     : https://prove2.me/submissions/37859a71-1031-4b9c-89aa-ba0a0124e850

import Definitions.Def_BitcoinVerify
import Theorems.Thm_BitcoinSig_parseScript_p2pkh
import Theorems.Thm_BitcoinScript_eval_pushes
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinSer_hash160_length

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

private theorem getD_app_lt {α : Type} (a b : List α) (i : Nat) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_app_ge {α : Type} (a b : List α) (i : Nat) (d : α) (h : a.length ≤ i) :
    (a ++ b).getD i d = b.getD (i - a.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem ofNat_toNat' (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem pushBytes_short (d : Bytes) (hd : d.length < 76) : pushBytes d = BitVec.ofNat 8 d.length :: d := by
  unfold pushBytes OP_PUSHDATA1; rw [if_pos hd]

/-- `IsPayToScriptHash` holds exactly on `OP_HASH160 <20 bytes> OP_EQUAL`. -/
theorem solution (s : Bytes) :
    BitcoinVerify.isPayToScriptHash s = true ↔ ∃ h : Bytes, h.length = 20 ∧ s = BitcoinVerify.p2shBytes h := by
  constructor
  · intro hs
    unfold isPayToScriptHash at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨hl, h0⟩, h1⟩, h22⟩ := hs
    match s, hl with
    | a :: b :: rest, hl =>
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h22
      simp only [List.length_cons] at hl
      have hne : rest ≠ [] := by intro e; subst e; simp at hl
      have e := (List.dropLast_concat_getLast hne).symm
      have hg : rest.getD 20 0 = rest.getLast hne := by
        rw [List.getD_eq_getElem?_getD, show (20:Nat) = rest.length - 1 by omega, ← List.getLast?_eq_getElem?,
          List.getLast?_eq_getLast hne]; rfl
      refine ⟨rest.dropLast, by simp; omega, ?_⟩
      have ha : a = 0xa9 := by have := ofNat_toNat' a; rw [h0] at this; exact this.symm
      have hb : b = BitVec.ofNat 8 rest.dropLast.length := by
        have := ofNat_toNat' b; rw [h1] at this; rw [show rest.dropLast.length = 0x14 by simp; omega]; exact this.symm
      have hc : rest.getLast hne = 0x87 := by
        rw [hg] at h22
        have := ofNat_toNat' (rest.getLast hne); rw [h22] at this; exact this.symm
      unfold p2shBytes
      rw [pushBytes_short _ (by simp; omega)]
      conv => lhs; rw [e, ha, hb, hc]
      simp
  · rintro ⟨h, hh, rfl⟩
    have e : p2shBytes h = 0xa9 :: 0x14 :: (h ++ [0x87]) := by
      unfold p2shBytes; rw [pushBytes_short _ (by rw [hh]; decide)]; rw [hh]; rfl
    rw [e]
    unfold isPayToScriptHash
    simp only [List.length_cons, List.length_append, List.length_nil, hh, List.getD_cons_zero, List.getD_cons_succ]
    rw [getD_app_ge _ _ _ _ (by omega), hh]
    decide
