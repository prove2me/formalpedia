-- Prove2me | solution 1 for BitcoinTaproot.checkSchnorr_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:41:46.371286+00:00
-- url     : https://prove2.me/submissions/7db030c0-5073-43c5-a2a8-f6a23b352911

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (tx : Tx) (spent : List TxOut) (nIn : Nat) (sig q : Bytes) (tapscript : Bool) (ed : ExecData) :
    BitcoinTaproot.checkSchnorrSignature tx spent nIn sig q tapscript ed = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr tx spent nIn ht tapscript ed = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by
  unfold checkSchnorrSignature
  by_cases hA : sig.length = 64
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [hA, if_neg (show ¬ (64 = 65) by decide), SIGHASH_DEFAULT]
    constructor
    · intro hm
      cases hs : sigHashSchnorr tx spent nIn 0 tapscript ed with
      | none => rw [hs] at hm; exact absurd hm (by simp)
      | some h => rw [hs] at hm; exact ⟨sig, 0, h, hA, Or.inl ⟨rfl, rfl⟩, hs, hm⟩
    · rintro ⟨body, ht, h, hb, hc, h1, h2⟩
      rcases hc with ⟨rfl, rfl⟩ | ⟨b, rfl, -, -⟩
      · rw [h1]; exact h2
      · simp at hA; omega
  · by_cases hB : sig.length = 65
    · rw [if_neg (by omega)]
      rcases List.eq_nil_or_concat sig with rfl | ⟨L, b, rfl⟩
      · simp at hB
      · have hL : L.length = 64 := by simp at hB; omega
        simp only [List.concat_eq_append] at *
        rw [hB]
        simp only [true_and, if_true, List.getLast?_concat, Option.getD_some, List.dropLast_concat, SIGHASH_DEFAULT]
        by_cases hb0 : b.toNat = 0
        · rw [if_pos hb0]
          simp only [Bool.false_eq_true, false_iff]
          rintro ⟨body, ht, h, hb, hc, -⟩
          rcases hc with ⟨he, -⟩ | ⟨b', he, h1, h2⟩
          · have := congrArg List.length he; simp at this; omega
          · obtain ⟨-, hbb⟩ := List.append_inj' he rfl
            simp at hbb; subst hbb; omega
        · rw [if_neg hb0]
          constructor
          · intro hm
            cases hs : sigHashSchnorr tx spent nIn b.toNat tapscript ed with
            | none => rw [hs] at hm; exact absurd hm (by simp)
            | some h => rw [hs] at hm; exact ⟨L, b.toNat, h, hL, Or.inr ⟨b, rfl, rfl, hb0⟩, hs, hm⟩
          · rintro ⟨body, ht, h, hb, hc, h1, h2⟩
            rcases hc with ⟨he, -⟩ | ⟨b', he, h3, h4⟩
            · have := congrArg List.length he; simp at this; omega
            · obtain ⟨rfl, hbb⟩ := List.append_inj' he rfl
              simp at hbb; subst hbb; subst h3
              rw [h1]; exact h2
    · rw [if_pos (by omega)]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨body, ht, h, hb, hc, -⟩
      rcases hc with ⟨rfl, -⟩ | ⟨b, rfl, -, -⟩
      · exact hA hb
      · simp at hB; omega
