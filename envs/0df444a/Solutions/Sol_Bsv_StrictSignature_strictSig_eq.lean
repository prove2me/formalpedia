-- Prove2me | solution 1 for Bsv.StrictSignature.strictSig_eq
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T11:40:24.473469+00:00
-- url     : https://prove2.me/submissions/d0f4f883-e6e4-4fd3-ab71-79959da7fd48

import Definitions.Def_bsv_strict_signature
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

open Bsv.StrictSignature

namespace Bsv.StrictSignature.Proof_strictSig_eq

theorem dropWhile_replicate_zero (k : Nat) (l : List Byte) :
    (List.replicate k 0#8 ++ l).dropWhile (· == 0#8) = l.dropWhile (· == 0#8) := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, List.dropWhile_cons, ih]

theorem msb_ne_zero (b : Byte) (h : b.msb = true) : (b == 0#8) = false := by
  cases hb : (b == 0#8)
  · rfl
  · have : b = 0#8 := by simpa using hb
    subst this
    simp at h

/-- The content bytes the parser accepts are the canonical ones for the value
it returns. -/
theorem canon_value (v0 : Byte) (vt : List Byte)
    (hneg : v0.msb = false) (hpad : padded v0 vt = false)
    (h33 : (vt.length == 32 && v0 != 0#8) = false) :
    canon (List.replicate (32 - (if vt.length == 32 then vt else v0 :: vt).length) 0#8 ++
      (if vt.length == 32 then vt else v0 :: vt)) = v0 :: vt := by
  unfold canon
  rw [dropWhile_replicate_zero]
  cases vt with
  | nil =>
    by_cases h0 : v0 = 0#8
    · subst h0; simp [List.dropWhile_cons]
    · simp [List.dropWhile_cons, h0, hneg]
  | cons v1 u =>
    by_cases h0 : v0 = 0#8
    · subst h0
      have hm : v1.msb = true := by simpa [padded] using hpad
      have hz := msb_ne_zero v1 hm
      have hz' : ¬ v1 = 0#8 := by simpa using hz
      by_cases hl : u.length = 31
      · simp [hl, List.dropWhile_cons, hz', hm]
      · simp [hl, List.dropWhile_cons, hz', hm]
    · have hl : ¬ u.length = 31 := by
        intro hl; simp [hl, h0] at h33
      simp [hl, List.dropWhile_cons, h0, hneg]

/-- An accepted INTEGER is the canonical encoding of its value, followed by
the unread remainder. -/
theorem strictInt_eq (b out rest : List Byte) (h : strictInt b = some (out, rest)) :
    b = encInt out ++ rest := by
  match b, h with
  | [], h => simp [strictInt] at h
  | [_], h => simp [strictInt] at h
  | tag :: len :: tl, h =>
    simp only [strictInt] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq, not_or,
        Decidable.not_not, Nat.not_lt] at hc
      obtain ⟨⟨⟨htag, _⟩, _⟩, hlen⟩ := hc
      have htake : (tl.take len.toNat).length = len.toNat := by
        simp only [List.length_take]; omega
      have hsplit : tl = tl.take len.toNat ++ tl.drop len.toNat :=
        (List.take_append_drop _ _).symm
      generalize tl.take len.toNat = v at h htake hsplit
      match v, h with
      | [], h => simp at h
      | v0 :: vt, h =>
        simp only at h
        split at h
        · simp at h
        · rename_i hneg
          split at h
          · simp at h
          · rename_i h33
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hout, hrest⟩ := h
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hneg
            have hcanon := canon_value v0 vt hneg.1 hneg.2 (by simpa using h33)
            rw [hout] at hcanon
            have hlenb : len = BitVec.ofNat 8 (v0 :: vt).length := by
              rw [htake]; simp
            rw [encInt, hcanon, ← hlenb, htag, hsplit, hrest]
            simp

end Bsv.StrictSignature.Proof_strictSig_eq

open Bsv.StrictSignature.Proof_strictSig_eq

theorem solution (b r s : List Byte) (h : strictSig b = some (r, s)) :
    b = encSig r s := by
  match b, h with
  | [], h => simp [strictSig] at h
  | [_], h => simp [strictSig] at h
  | seq :: len :: body, h =>
    simp only [strictSig] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hc
      obtain ⟨hseq, hlen⟩ := hc
      split at h
      · simp at h
      · rename_i r' body1 hr
        split at h
        · simp at h
        · rename_i s' body2 hs
          split at h
          · rename_i hemp
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have e1 := strictInt_eq _ _ _ hr
            have e2 := strictInt_eq _ _ _ hs
            have hb2 : body2 = [] := by simpa using hemp
            subst hb2
            have hbody : body = encInt r' ++ encInt s' := by rw [e1, e2]; simp
            have hlenb : len = BitVec.ofNat 8 body.length := by rw [← hlen]; simp
            rw [encSig, ← hbody, ← hlenb, hseq]
          · simp at h
