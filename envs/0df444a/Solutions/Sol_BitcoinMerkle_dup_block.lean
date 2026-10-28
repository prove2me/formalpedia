-- Prove2me | solution 1 for BitcoinMerkle.dup_block
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:03.856257+00:00
-- url     : https://prove2.me/submissions/805036fe-fd40-43d0-a54f-41af6a54a718

import Definitions.Def_BitcoinMerkle
import Theorems.Thm_BitcoinMerkle_rootLoop_fst
import Theorems.Thm_BitcoinMerkle_rootLoop_sticky
import Theorems.Thm_BitcoinMerkle_pairUp_append_even
import Theorems.Thm_BitcoinMerkle_hasEqualPair_append_even

open BitcoinMerkle

/-- One iteration of the loop. -/
private theorem rootLoop_step {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = BitcoinMerkle.rootLoop c z (BitcoinMerkle.pairUp c hs) (m || BitcoinMerkle.hasEqualPair hs) := by
  conv => lhs; rw [rootLoop]
  rw [dif_pos h]

/-- General form of CVE-2012-2459: duplicating an aligned block of `2 ^ k` leaves at the end of
the list leaves the root unchanged and is detected by the mutation flag. -/
theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    ∀ (k : Nat) (l t : List H), l ≠ [] → l.length % 2 ^ (k + 1) = 0 → t.length = 2 ^ k →
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t)).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).1 ∧
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).2 = true := by
  suffices key : ∀ (k : Nat) (l t : List H) (m : Bool), l ≠ [] → l.length % 2 ^ (k + 1) = 0 → t.length = 2 ^ k →
      (rootLoop c z (l ++ t) m).1 = (rootLoop c z (l ++ t ++ t) m).1 ∧
      (rootLoop c z (l ++ t ++ t) m).2 = true by
    intro k l t hne hl ht
    exact key k l t false hne hl ht
  intro k
  induction k with
  | zero =>
    intro l t m hne hl ht
    simp only [Nat.zero_add, Nat.pow_one, Nat.pow_zero] at hl ht
    rcases t with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp at ht
    rotate_left
    · simp at ht
    have hlen : 0 < l.length := List.length_pos_iff.2 hne
    have hp : pairUp c (l ++ [a]) = pairUp c (l ++ [a, a]) := by
      rw [BitcoinMerkle.pairUp_append_even c l [a] hl, BitcoinMerkle.pairUp_append_even c l [a, a] hl]
      simp [pairUp]
    have hq : hasEqualPair (l ++ [a, a]) = true := by
      rw [BitcoinMerkle.hasEqualPair_append_even l [a, a] hl]
      simp [hasEqualPair]
    have e : l ++ [a] ++ [a] = l ++ [a, a] := by simp
    have h1 : 1 < (l ++ [a]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have h2 : 1 < (l ++ [a, a]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [e]
    constructor
    · rw [rootLoop_step c z _ m h1, rootLoop_step c z _ m h2, hp]
      exact BitcoinMerkle.rootLoop_fst c z _ _ _
    · rw [rootLoop_step c z _ m h2, hq]
      simp only [Bool.or_true]
      exact BitcoinMerkle.rootLoop_sticky c z _
  | succ k ih =>
    intro l t m hne hl ht
    have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 := Nat.pow_succ ..
    have hteven : t.length % 2 = 0 := by rw [ht, Nat.pow_succ]; simp
    rw [hpow] at hl
    have hdvd : 2 ∣ 2 ^ (k + 1) * 2 := ⟨2 ^ (k + 1), Nat.mul_comm _ _⟩
    have hleven : l.length % 2 = 0 := by
      rw [← Nat.mod_mod_of_dvd l.length hdvd, hl]
    have hlen : 0 < l.length := List.length_pos_iff.2 hne
    have htpos : 0 < t.length := by rw [ht]; exact Nat.two_pow_pos _
    have hl' : (pairUp c l).length % 2 ^ (k + 1) = 0 := by
      rw [pairUp_length]
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hl
      rw [hq]
      have e : 2 ^ (k + 1) * 2 * q + 1 = 2 * (2 ^ (k + 1) * q) + 1 := by
        rw [Nat.mul_comm (2 ^ (k + 1)) 2, Nat.mul_assoc]
      rw [e, Nat.mul_add_div (by decide), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero,
        Nat.mul_mod_right]
    have ht' : (pairUp c t).length = 2 ^ k := by
      rw [pairUp_length, ht, Nat.pow_succ]; omega
    have hne' : pairUp c l ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [pairUp_length] at this
      simp at this
      omega
    have hp1 : pairUp c (l ++ t) = pairUp c l ++ pairUp c t :=
      BitcoinMerkle.pairUp_append_even c l t hleven
    have hlt_even : (l ++ t).length % 2 = 0 := by
      simp only [List.length_append]; omega
    have hp2 : pairUp c (l ++ t ++ t) = pairUp c l ++ pairUp c t ++ pairUp c t := by
      rw [BitcoinMerkle.pairUp_append_even c (l ++ t) t hlt_even, hp1]
    have h1 : 1 < (l ++ t).length := by
      simp only [List.length_append]; omega
    have h2 : 1 < (l ++ t ++ t).length := by
      simp only [List.length_append]; omega
    obtain ⟨ihr, ihm⟩ := ih (pairUp c l) (pairUp c t) (m || hasEqualPair (l ++ t ++ t)) hne' hl' ht'
    constructor
    · rw [rootLoop_step c z _ m h1, rootLoop_step c z _ m h2, hp1, hp2]
      rw [BitcoinMerkle.rootLoop_fst c z _ (m || hasEqualPair (l ++ t)) (m || hasEqualPair (l ++ t ++ t))]
      exact ihr
    · rw [rootLoop_step c z _ m h2, hp2]
      exact ihm
