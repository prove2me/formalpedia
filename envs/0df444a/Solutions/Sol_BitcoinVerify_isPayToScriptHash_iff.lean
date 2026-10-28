-- Prove2me | solution 1 for BitcoinVerify.isPayToScriptHash_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:42:33.258802+00:00
-- url     : https://prove2.me/submissions/d658b77b-cca3-4efd-ad75-0a755f1192f8

import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem S189B_tn (k : Nat) (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  simp [BitVec.toNat_ofNat]; omega

theorem S189B_pb_small (d : Bytes) (h : d.length < 76) : pushBytes d = BitVec.ofNat 8 d.length :: d := by
  simp [pushBytes, OP_PUSHDATA1, h]

theorem S189B_p2sh_eq (h : Bytes) (hh : h.length = 20) :
    p2shBytes h = 0xa9 :: 0x14 :: (h ++ [0x87]) := by
  simp [p2shBytes, S189B_pb_small h (by omega), hh]

theorem S189B_p2sh_iff (s : Bytes) :
    BitcoinVerify.isPayToScriptHash s = true ↔ ∃ h : Bytes, h.length = 20 ∧ s = BitcoinVerify.p2shBytes h := by
  constructor
  · intro H
    simp only [isPayToScriptHash, Bool.and_eq_true, decide_eq_true_eq] at H
    obtain ⟨⟨⟨hl, h0⟩, h1⟩, h22⟩ := H
    rcases s with _ | ⟨a0, _ | ⟨a1, t⟩⟩
    · simp at hl
    · simp at hl
    simp only [List.length_cons] at hl
    have ht : t ≠ [] := by intro e; subst e; simp at hl
    obtain ⟨h, l, rfl⟩ : ∃ h l, t = h ++ [l] := ⟨_, _, (List.dropLast_concat_getLast ht).symm⟩
    have hd : h.length = 20 := by simp at hl; omega
    refine ⟨h, hd, ?_⟩
    rw [S189B_p2sh_eq _ hd]
    have ea0 : a0 = 0xa9 := BitVec.eq_of_toNat_eq (by simpa using h0)
    have ea1 : a1 = 0x14 := BitVec.eq_of_toNat_eq (by simpa using h1)
    subst ea0 ea1
    have : (BitVec.ofNat 8 0xa9 :: BitVec.ofNat 8 0x14 :: (h ++ [l])).getD 22 0 = l := by
      simp [List.getD_eq_getElem?_getD, hd]
    rw [show (0xa9 : BitVec 8) = BitVec.ofNat 8 0xa9 from rfl, show (0x14 : BitVec 8) = BitVec.ofNat 8 0x14 from rfl, this] at h22
    have el : l = 0x87 := BitVec.eq_of_toNat_eq (by simpa using h22)
    subst el; rfl
  · rintro ⟨h, hh, rfl⟩
    rw [S189B_p2sh_eq _ hh]
    have : (BitVec.ofNat 8 0xa9 :: BitVec.ofNat 8 0x14 :: (h ++ [(0x87 : BitVec 8)])).getD 22 0 = 0x87 := by
      simp [List.getD_eq_getElem?_getD, hh]
    simp only [isPayToScriptHash, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by simp [hh], rfl⟩, rfl⟩, ?_⟩
    rw [show (0xa9 : BitVec 8) = BitVec.ofNat 8 0xa9 from rfl, show (0x14 : BitVec 8) = BitVec.ofNat 8 0x14 from rfl, this]
    rfl

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem solution (s : Bytes) :
    BitcoinVerify.isPayToScriptHash s = true ↔ ∃ h : Bytes, h.length = 20 ∧ s = BitcoinVerify.p2shBytes h := by
  exact S189B_p2sh_iff s
