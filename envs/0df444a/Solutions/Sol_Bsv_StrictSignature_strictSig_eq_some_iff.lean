-- Prove2me | solution 1 for Bsv.StrictSignature.strictSig_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:27:15.555035+00:00
-- url     : https://prove2.me/submissions/2cac074d-f25d-4371-ae50-f3165745231c

import Definitions.Def_bsv_strict_signature
import Theorems.Thm_Bsv_StrictSignature_strictSig_encSig
import Theorems.Thm_Bsv_StrictSignature_strictSig_eq
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
-/

namespace Bsv.StrictSignature.Proof_strictSig_eq_some_iff

section

/-- A value returned for an INTEGER field is 32 bytes long. -/
theorem strictInt_length (b out rest : List Byte) (h : strictInt b = some (out, rest)) :
    out.length = 32 := by
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
      obtain ⟨⟨⟨_, _⟩, hn⟩, hlen⟩ := hc
      have htake : (tl.take len.toNat).length = len.toNat := by
        simp only [List.length_take]; omega
      generalize tl.take len.toNat = v at h htake
      match v, h with
      | [], h => simp at h
      | v0 :: vt, h =>
        simp only at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hout, _⟩ := h
            rw [← hout]
            simp only [List.length_cons] at htake
            by_cases h32 : vt.length = 32
            · simp [h32]
            · simp [h32]; omega

/-- Both values returned by the parser are 32 bytes long. -/
theorem strictSig_lengths (b r s : List Byte) (h : strictSig b = some (r, s)) :
    r.length = 32 ∧ s.length = 32 := by
  match b, h with
  | [], h => simp [strictSig] at h
  | [_], h => simp [strictSig] at h
  | seq :: len :: body, h =>
    simp only [strictSig] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i r' body1 hr
        split at h
        · simp at h
        · rename_i s' body2 hs
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨strictInt_length _ _ _ hr, strictInt_length _ _ _ hs⟩
          · simp at h

/-- **What the parser accepts, completely.** It returns `(r, s)` for `b` exactly
when both are 32 bytes and `b` is the encoder's output for them. -/
theorem strictSig_eq_some_iff (b r s : List Byte) :
    strictSig b = some (r, s) ↔ r.length = 32 ∧ s.length = 32 ∧ b = encSig r s := by
  constructor
  · intro h
    have hl := strictSig_lengths b r s h
    exact ⟨hl.1, hl.2, strictSig_eq b r s h⟩
  · rintro ⟨hr, hs, rfl⟩
    exact strictSig_encSig r s hr hs

end

end Bsv.StrictSignature.Proof_strictSig_eq_some_iff

open Bsv.StrictSignature

theorem solution (b r s : List Byte) :
    strictSig b = some (r, s) ↔ r.length = 32 ∧ s.length = 32 ∧ b = encSig r s :=
  Bsv.StrictSignature.Proof_strictSig_eq_some_iff.strictSig_eq_some_iff b r s
