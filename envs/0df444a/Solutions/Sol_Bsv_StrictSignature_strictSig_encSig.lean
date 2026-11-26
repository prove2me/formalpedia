-- Prove2me | solution 1 for Bsv.StrictSignature.strictSig_encSig
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:26:44.713468+00:00
-- url     : https://prove2.me/submissions/a0af3ac1-b2cd-493e-bc3f-a6566b1762e3

import Definitions.Def_bsv_strict_signature
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
-/

namespace Bsv.StrictSignature.Proof_strictSig_encSig

section

/-- A byte string is its leading zeros followed by what remains after them. -/
theorem split_zeros (l : List Byte) :
    l = List.replicate (l.length - (l.dropWhile (· == 0#8)).length) 0#8 ++
      l.dropWhile (· == 0#8) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a = 0#8
    · subst ha
      have hle : (t.dropWhile (· == 0#8)).length ≤ t.length :=
        (List.dropWhile_sublist _).length_le
      simp only [List.dropWhile_cons, beq_self_eq_true, ite_true, List.length_cons]
      rw [Nat.succ_sub hle, List.replicate_succ, List.cons_append, ← ih]
    · simp [List.dropWhile_cons, ha]

/-- What remains after the leading zeros does not start with zero. -/
theorem head_dropWhile_ne_zero : ∀ (l : List Byte) (h : Byte) (t : List Byte),
    l.dropWhile (· == 0#8) = h :: t → h ≠ 0#8
  | [], _, _, hd => by simp at hd
  | a :: l, h, t, hd => by
    by_cases ha : a = 0#8
    · subst ha
      simp only [List.dropWhile_cons, beq_self_eq_true, ite_true] at hd
      exact head_dropWhile_ne_zero l h t hd
    · simp [List.dropWhile_cons, ha] at hd
      rw [← hd.1]
      exact ha

theorem canon_length_le (x : List Byte) : (canon x).length ≤ x.length + 1 := by
  have hle : (x.dropWhile (· == 0#8)).length ≤ x.length := (List.dropWhile_sublist _).length_le
  unfold canon
  split
  · simp
  · rename_i h t hd
    rw [hd] at hle
    simp only [List.length_cons] at hle
    split <;> simp <;> omega

/-- The parser on an INTEGER field whose content satisfies its three rules. -/
theorem strictInt_of (v0 : Byte) (vt rest : List Byte) (hn33 : vt.length + 1 ≤ 33)
    (hmsb : v0.msb = false) (hpad : padded v0 vt = false)
    (h33 : (vt.length == 32 && v0 != 0#8) = false) :
    strictInt (0x02#8 :: BitVec.ofNat 8 (v0 :: vt).length :: ((v0 :: vt) ++ rest)) =
      some (List.replicate (32 - (if vt.length == 32 then vt else v0 :: vt).length) 0#8 ++
        (if vt.length == 32 then vt else v0 :: vt), rest) := by
  have hn : (BitVec.ofNat 8 (v0 :: vt).length).toNat = (v0 :: vt).length := by
    simp only [List.length_cons, BitVec.toNat_ofNat]; omega
  have htake : ((v0 :: vt) ++ rest).take (v0 :: vt).length = v0 :: vt := by simp
  have hdrop : ((v0 :: vt) ++ rest).drop (v0 :: vt).length = rest := by simp
  have hc : (0x02#8 != 0x02#8 || (v0 :: vt).length == 0 || decide ((v0 :: vt).length > 33)
      || decide (((v0 :: vt) ++ rest).length < (v0 :: vt).length)) = false := by
    simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not, List.length_cons, List.length_append]
    omega
  simp only [strictInt, hn, hc, htake, hdrop, hmsb, hpad, h33, Bool.false_or,
    Bool.false_eq_true, ite_false]

/-- Reading the encoding of a 32-byte value returns that value and what follows. -/
theorem strictInt_encInt (r : List Byte) (hr : r.length = 32) (rest : List Byte) :
    strictInt (encInt r ++ rest) = some (r, rest) := by
  have hsplit := split_zeros r
  cases hd : r.dropWhile (· == 0#8) with
  | nil =>
    rw [hd] at hsplit
    simp only [List.length_nil, Nat.sub_zero, List.append_nil, hr] at hsplit
    have hc : canon r = [0#8] := by simp [canon, hd]
    unfold encInt
    rw [hc]
    refine (strictInt_of 0#8 [] rest (by simp) (by decide) rfl rfl).trans ?_
    rw [hsplit]
    rfl
  | cons h t =>
    have hlen : (h :: t).length ≤ 32 := by
      rw [← hd, ← hr]; exact (List.dropWhile_sublist _).length_le
    have hr' : r = List.replicate (32 - (h :: t).length) 0#8 ++ (h :: t) := by
      rw [hd, hr] at hsplit; exact hsplit
    have hh : h ≠ 0#8 := head_dropWhile_ne_zero r h t hd
    simp only [List.length_cons] at hlen
    by_cases hm : h.msb = true
    · -- a zero byte is put back in front
      have hc : canon r = 0#8 :: h :: t := by simp [canon, hd, hm]
      unfold encInt
      rw [hc]
      refine (strictInt_of 0#8 (h :: t) rest (by simp; omega) (by decide)
        (by simp [padded, hm]) (by simp)).trans ?_
      by_cases h32 : (h :: t).length = 32
      · rw [if_pos (by simpa using h32), ← hr']
      · rw [if_neg (by simpa using h32)]
        have e : 32 - (h :: t).length = (32 - (0#8 :: h :: t).length) + 1 := by
          simp only [List.length_cons] at h32 ⊢; omega
        have : List.replicate (32 - (0#8 :: h :: t).length) 0#8 ++ (0#8 :: h :: t) = r := by
          conv => rhs; rw [hr', e, List.replicate_succ', List.append_assoc]
          rfl
        rw [this]
    · have hm' : h.msb = false := by simpa using hm
      have hc : canon r = h :: t := by simp [canon, hd, hm']
      unfold encInt
      rw [hc]
      have hpad : padded h t = false := by
        cases t with
        | nil => rfl
        | cons a u => simp [padded, hh]
      have ht : ¬ t.length = 32 := by omega
      refine (strictInt_of h t rest (by omega) hm' hpad (by simp [ht])).trans ?_
      rw [if_neg (by simpa using ht), ← hr']

/-- **Every output of the encoder is accepted**, for 32-byte values, and returns
the pair that was encoded. -/
theorem strictSig_encSig (r s : List Byte) (hr : r.length = 32) (hs : s.length = 32) :
    strictSig (encSig r s) = some (r, s) := by
  have h1 := strictInt_encInt r hr (encInt s)
  have h2 := strictInt_encInt s hs []
  rw [List.append_nil] at h2
  have hbody : (BitVec.ofNat 8 (encInt r ++ encInt s).length).toNat
      = (encInt r ++ encInt s).length := by
    have a := canon_length_le r
    have b := canon_length_le s
    simp only [encInt, BitVec.toNat_ofNat, List.length_append, List.length_cons]
    omega
  simp only [encSig, strictSig, hbody, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
    ite_false, h1, h2, List.isEmpty_nil, ite_true]

end

end Bsv.StrictSignature.Proof_strictSig_encSig

open Bsv.StrictSignature

theorem solution (r s : List Byte) (hr : r.length = 32) (hs : s.length = 32) :
    strictSig (encSig r s) = some (r, s) :=
  Bsv.StrictSignature.Proof_strictSig_encSig.strictSig_encSig r s hr hs
