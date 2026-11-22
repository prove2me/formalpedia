-- Prove2me | solution 1 for Bernstein.curve25519_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:59:38.458798+00:00
-- url     : https://prove2.me/submissions/6ddcce3d-2edc-490f-a9f4-44eb9513e479

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Theorems.Thm_Bernstein_theorem_2_1
import Theorems.Thm_Bernstein_not_isSquare_two_and_disc

set_option autoImplicit false

namespace Bernstein.Spec

theorem sum_digits (s : ℕ) :
    ∀ k, ∑ i ∈ Finset.range k, (s / 256 ^ i % 256) * 256 ^ i = s % 256 ^ k
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by rw [Finset.sum_range_succ, sum_digits s k, Nat.mod_pow_succ]; ring

theorem ofBytes_bytes (s : ℕ) (hs : s < 2 ^ 256) : ofBytes (bytes s) = s := by
  unfold ofBytes bytes
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun i => s / 256 ^ i % 256 * 256 ^ i) 32, sum_digits,
    Nat.mod_eq_of_lt]
  norm_num at hs ⊢; exact hs

theorem bytes_bijective : Function.Bijective (fun s : Fin (2 ^ 256) => bytes s) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ?_, by simp⟩
  have := congrArg ofBytes hab
  simp only at this
  rw [ofBytes_bytes a a.2, ofBytes_bytes b b.2] at this
  exact Fin.ext this

theorem exists_bytes (b : Fin 32 → Fin 256) : ∃ s : ℕ, s < 2 ^ 256 ∧ bytes s = b := by
  obtain ⟨s, hs⟩ := bytes_bijective.2 b
  exact ⟨s, s.2, hs⟩

theorem secretKeyBytes_iff (b : Fin 32 → Fin 256) :
    b ∈ secretKeyBytes ↔ ofBytes b ∈ secretKeys := by
  obtain ⟨s, hs, rfl⟩ := exists_bytes b
  rw [ofBytes_bytes s hs]
  simp only [secretKeyBytes, secretKeys, bytes, Set.mem_ofPred_eq]
  norm_num at hs ⊢
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨(s - 2 ^ 254) / 8, by norm_num; omega, by norm_num; omega⟩
  · rintro ⟨i, hi, rfl⟩
    omega

theorem p25519_ge_five : 5 ≤ p25519 := by unfold p25519; norm_num

/-- `Curve25519(n, q)` is the unique admissible `s`, from Theorem 2.1. -/
theorem curve25519_main [Fact p25519.Prime] (n q : ℕ) :
    (∃! s : ℕ, s ≤ 2 ^ 255 - 20 ∧
        ∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
          X0 ((n : ℤ) • Q) = emb p25519 (s : ZMod p25519)) ∧
      curve25519 n q ≤ 2 ^ 255 - 20 ∧
      (∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
        X0 ((n : ℤ) • Q) = emb p25519 (curve25519 n q : ZMod p25519)) := by
  obtain ⟨s, hs, huniq⟩ := theorem_2_1 p25519 p25519_ge_five A25519
    (not_isSquare_two_and_disc).2.2 (n : ℤ) (q : ZMod p25519)
  have hlt : s.val < 2 ^ 255 - 19 := ZMod.val_lt s
  have hle : s.val ≤ 2 ^ 255 - 20 := by norm_num at hlt ⊢; omega
  have key : ∀ t : ℕ, (t ≤ 2 ^ 255 - 20 ∧
      ∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
        X0 ((n : ℤ) • Q) = emb p25519 (t : ZMod p25519)) ↔ t = s.val := by
    intro t
    constructor
    · rintro ⟨ht, hQ⟩
      have e := huniq (t : ZMod p25519) hQ
      have htp : t < p25519 := by unfold p25519; omega
      rw [← e, ZMod.val_cast_of_lt htp]
    · rintro rfl
      exact ⟨hle, by rw [ZMod.natCast_zmod_val]; exact hs⟩
  have hc : curve25519 n q = s.val := by
    unfold curve25519
    refine (congrArg sInf (Set.ext fun t => ?_)).trans (csInf_singleton s.val)
    exact (key t).trans Set.mem_singleton_iff.symm
  refine ⟨⟨s.val, (key _).2 rfl, fun t ht => (key t).1 ht⟩, ?_, ?_⟩
  · rw [hc]; exact hle
  · rw [hc]; exact ((key _).2 rfl).2

theorem byte31_lt [Fact p25519.Prime] (n q : ℕ) :
    ((bytes (curve25519 n q)) 31 : ℕ) < 128 := by
  have h := (curve25519_main n q).2.1
  simp only [bytes]
  norm_num at h ⊢
  omega

theorem curve25519_spec_dev [Fact p25519.Prime] :
    (∀ s : ℕ, s < 2 ^ 256 → ofBytes (bytes s) = s) ∧
    (∀ b : Fin 32 → Fin 256, ofBytes b < 2 ^ 256 ∧ bytes (ofBytes b) = b) ∧
    (∀ b : Fin 32 → Fin 256, b ∈ secretKeyBytes ↔ ofBytes b ∈ secretKeys) ∧
    (∀ n q : ℕ, n ∈ secretKeys → q < 2 ^ 256 →
      (∃! s : ℕ, s ≤ 2 ^ 255 - 20 ∧
        ∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
          X0 ((n : ℤ) • Q) = emb p25519 (s : ZMod p25519)) ∧
      curve25519 n q ≤ 2 ^ 255 - 20 ∧
      (∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
        X0 ((n : ℤ) • Q) = emb p25519 (curve25519 n q : ZMod p25519)) ∧
      ((curve25519Bytes (bytes n) (bytes q) 31 : ℕ) < 128)) ∧
    (∀ b c : Fin 32 → Fin 256, b ∈ secretKeyBytes → (curve25519Bytes b c 31 : ℕ) < 128) ∧
    ¬ ∀ d : Fin 32 → Fin 256, ∃ b c : Fin 32 → Fin 256, b ∈ secretKeyBytes ∧
      curve25519Bytes b c = d := by
  have hall : ∀ b c : Fin 32 → Fin 256, (curve25519Bytes b c 31 : ℕ) < 128 :=
    fun b c => byte31_lt _ _
  refine ⟨ofBytes_bytes, fun b => ?_, secretKeyBytes_iff, fun n q hn hq => ?_,
    fun b c _ => hall b c, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := exists_bytes b
    rw [ofBytes_bytes s hs]; exact ⟨hs, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := hn
    exact ⟨(curve25519_main _ q).1, (curve25519_main _ q).2.1, (curve25519_main _ q).2.2,
      hall _ _⟩
  · intro h
    obtain ⟨b, c, -, hbc⟩ := h (fun _ => 128)
    have := hall b c
    rw [hbc] at this
    simp at this

end Bernstein.Spec

open Bernstein Bernstein.Spec in
theorem solution [Fact p25519.Prime] :
    (∀ s : ℕ, s < 2 ^ 256 → ofBytes (bytes s) = s) ∧
    (∀ b : Fin 32 → Fin 256, ofBytes b < 2 ^ 256 ∧ bytes (ofBytes b) = b) ∧
    (∀ b : Fin 32 → Fin 256, b ∈ secretKeyBytes ↔ ofBytes b ∈ secretKeys) ∧
    (∀ n q : ℕ, n ∈ secretKeys → q < 2 ^ 256 →
      (∃! s : ℕ, s ≤ 2 ^ 255 - 20 ∧
        ∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
          X0 ((n : ℤ) • Q) = emb p25519 (s : ZMod p25519)) ∧
      curve25519 n q ≤ 2 ^ 255 - 20 ∧
      (∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
        X0 ((n : ℤ) • Q) = emb p25519 (curve25519 n q : ZMod p25519)) ∧
      ((curve25519Bytes (bytes n) (bytes q) 31 : ℕ) < 128)) ∧
    (∀ b c : Fin 32 → Fin 256, b ∈ secretKeyBytes → (curve25519Bytes b c 31 : ℕ) < 128) ∧
    ¬ ∀ d : Fin 32 → Fin 256, ∃ b c : Fin 32 → Fin 256, b ∈ secretKeyBytes ∧
      curve25519Bytes b c = d :=
  curve25519_spec_dev
