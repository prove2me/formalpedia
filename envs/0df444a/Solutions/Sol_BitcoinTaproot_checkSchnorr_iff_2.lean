-- Prove2me | solution 2 for BitcoinTaproot.checkSchnorr_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:16.168418+00:00
-- url     : https://prove2.me/submissions/9bffac6f-1022-41b2-b5f4-c59fd6274561

import Definitions.Def_BitcoinTaproot

open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

private theorem lexLt_asymm : ∀ (a b : Bytes), lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [lexLt] at h
  | x :: xs, y :: ys, h => by
    simp only [lexLt] at h ⊢
    by_cases h1 : x.toNat < y.toNat
    · rw [if_neg (by omega), if_pos h1]
    · rw [if_neg h1] at h
      by_cases h2 : y.toNat < x.toNat
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [if_neg h2, if_neg h1]
        exact lexLt_asymm xs ys h

private theorem lexLt_total : ∀ (a b : Bytes), lexLt a b = false → lexLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [lexLt] at h
  | _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [lexLt] at h1 h2
    by_cases hxy : x.toNat < y.toNat
    · rw [if_pos hxy] at h1; cases h1
    · rw [if_neg hxy] at h1
      by_cases hyx : y.toNat < x.toNat
      · rw [if_pos hyx] at h2; cases h2
      · rw [if_neg hyx] at h1
        rw [if_neg hyx, if_neg hxy] at h2
        have hx : x = y := by
          have : x.toNat = y.toNat := by omega
          exact BitVec.eq_of_toNat_eq this
        rw [hx, lexLt_total xs ys h1 h2]

/-- The Schnorr checker, unfolded: a 64-byte signature with `SIGHASH_DEFAULT`, or a 65-byte one
whose last byte is a non-zero hash type, verifying under BIP340 against the BIP341 hash. -/
theorem solution (tx : Tx) (spent : List TxOut) (nIn : Nat) (sig q : Bytes) (tapscript : Bool) (ed : ExecData) :
    BitcoinTaproot.checkSchnorrSignature tx spent nIn sig q tapscript ed = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr tx spent nIn ht tapscript ed = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by
  unfold checkSchnorrSignature
  dsimp only
  by_cases h64 : sig.length = 64
  · rw [if_neg (by omega)]
    simp only [h64, show ¬ ((64:Nat) = 65) by omega, ite_false, false_and, SIGHASH_DEFAULT]
    constructor
    · intro h
      cases hh : sigHashSchnorr tx spent nIn 0 tapscript ed with
      | none => rw [hh] at h; cases h
      | some hv => rw [hh] at h; exact ⟨sig, 0, hv, h64, Or.inl ⟨rfl, rfl⟩, hh, h⟩
    · rintro ⟨body, ht, hv, hl, hd, hh, hs⟩
      rcases hd with ⟨rfl, rfl⟩ | ⟨b, rfl, _, _⟩
      · rw [hh]; exact hs
      · simp at h64; omega
  · by_cases h65 : sig.length = 65
    · rw [if_neg (by omega)]
      obtain ⟨body, b, rfl⟩ : ∃ body b, sig = body ++ [b] := by
        match sig, h65 with
        | [], h => simp at h
        | s :: ss, _ => exact ⟨(s :: ss).dropLast, (s :: ss).getLast (by simp), (List.dropLast_concat_getLast _).symm⟩
      have hb65 : body.length = 64 := by simp at h65; omega
      simp only [h65, ite_true, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some,
        List.dropLast_concat, SIGHASH_DEFAULT, true_and]
      constructor
      · intro h
        by_cases hb : b.toNat = 0
        · rw [if_pos hb] at h; cases h
        · rw [if_neg hb] at h
          cases hh : sigHashSchnorr tx spent nIn b.toNat tapscript ed with
          | none => rw [hh] at h; cases h
          | some hv =>
            rw [hh] at h
            exact ⟨body, b.toNat, hv, hb65, Or.inr ⟨b, rfl, rfl, hb⟩, hh, h⟩
      · rintro ⟨s2, ht, hv, hl, hd, hh, hs⟩
        rcases hd with ⟨he, rfl⟩ | ⟨b2, he, hbt, hne⟩
        · have := congrArg List.length he; simp at this; omega
        · have e := List.append_inj_right he (by omega)
          have e2 := List.append_inj_left he (by omega)
          simp only [List.cons.injEq, and_true] at e
          subst e; subst e2
          rw [if_neg (by rw [hbt]; exact hne), hbt, hh]; exact hs
    · rw [if_pos ⟨h64, h65⟩]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨body, ht, hv, hl, hd, _, _⟩
      rcases hd with ⟨rfl, _⟩ | ⟨b, rfl, _, _⟩
      · exact h64 hl
      · simp at h65; omega
