-- Prove2me | solution 1 for Erdos195.no_two_chain_only_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-17T16:33:33.545175+00:00
-- url     : https://prove2.me/submissions/c95c3571-eabf-404b-84bf-c2a9205cdce4

import Definitions.Def_Erdos195_tree
import Theorems.Thm_Erdos195_forced_escape_prefix
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Erdos195

private lemma x_form {x : ℤ} (hxmod : x % 4 = 3) : x = 4 * (x / 4) + 3 := by
  have h := Int.ediv_mul_add_emod x 4
  rw [hxmod, mul_comm] at h
  linarith

private lemma x_odd {x : ℤ} (hxmod : x % 4 = 3) : x % 2 = 1 := by
  have hx := x_form hxmod
  omega

private lemma not_dvd_two_of_ge_three {x : ℤ} (hx : (3 : ℤ) ≤ x) : ¬ x ∣ (2 : ℤ) := by
  intro hdv
  obtain ⟨k, hk⟩ := hdv
  have hnn : 0 ≤ x := le_trans (by decide : (0 : ℤ) ≤ 3) hx
  have habs : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hnn
  have hge : 3 ≤ x.natAbs := by
    have : (3 : ℤ) ≤ x.natAbs := by
      simpa [habs] using hx
    exact_mod_cast this
  have hmul : x.natAbs * k.natAbs = 2 := by
    have := congrArg Int.natAbs hk
    rw [Int.natAbs_mul] at this
    have h2 : Int.natAbs (2 : ℤ) = 2 := rfl
    rw [h2] at this
    exact this.symm
  have hdiv : x.natAbs ∣ 2 := ⟨k.natAbs, hmul.symm⟩
  have : x.natAbs ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

private lemma three_pow_ge_nine (n : ℕ) : (9 : ℤ) ≤ (3 : ℤ) ^ (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    nlinarith

private lemma three_pow_ne_five (n : ℕ) : (3 : ℤ) ^ n ≠ 5 := by
  intro h
  match n with
  | 0 => cases h
  | 1 => cases h
  | n + 2 =>
    have := three_pow_ge_nine n
    rw [h] at this
    linarith

private lemma three_pow_ne_seven (n : ℕ) : (3 : ℤ) ^ n ≠ 7 := by
  intro h
  match n with
  | 0 => cases h
  | 1 => cases h
  | n + 2 =>
    have := three_pow_ge_nine n
    rw [h] at this
    linarith

private lemma not_in_Sx_escape {x : ℤ} (hx : (3 : ℤ) ≤ x) :
    (∀ n : ℕ, 3 * x - 2 ≠ (3 : ℤ) ^ n ∧ 3 * x - 2 ≠ x * (3 : ℤ) ^ n) ∧
    (∀ n : ℕ, 5 * x ≠ (3 : ℤ) ^ n ∧ 5 * x ≠ x * (3 : ℤ) ^ n) ∧
    (∀ n : ℕ, 7 * x ≠ (3 : ℤ) ^ n ∧ 7 * x ≠ x * (3 : ℤ) ^ n) := by
  have hx0 : x ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · intro h
      have hn0 : n ≠ 0 := by
        intro hn
        subst hn
        have : 3 * x - 2 = 1 := by simpa using h
        linarith
      have hmod : (3 * x - 2) % 3 = 1 := by
        have hx3 : (3 * x) % 3 = 0 := by
          rw [Int.mul_emod, Int.emod_self]
          simp
        omega
      have hpow : ((3 : ℤ) ^ n) % 3 = 0 := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        subst hm
        rw [pow_succ, Int.mul_emod, Int.emod_self]
        simp
      have : (3 * x - 2) % 3 = 0 := by rw [h, hpow]
      omega
    · intro h
      have : x ∣ 3 * x - 2 := by
        rw [h]
        exact dvd_mul_right _ _
      have : x ∣ (2 : ℤ) := by
        have h3x : x ∣ 3 * x := dvd_mul_left _ _
        have hsub := dvd_sub h3x this
        simpa using hsub
      exact not_dvd_two_of_ge_three hx this
  · intro n
    refine ⟨?_, ?_⟩
    · intro h
      have h5 : (5 : ℤ) ∣ (3 : ℤ) ^ n := ⟨x, by linarith⟩
      have h5N : (5 : ℕ) ∣ (3 : ℕ) ^ n := by exact_mod_cast h5
      have : 5 ∣ 3 := Nat.prime_five.dvd_of_dvd_pow h5N
      omega
    · intro h
      have h' : x * 5 = x * (3 : ℤ) ^ n := by simpa [mul_comm] using h
      have heq : (5 : ℤ) = (3 : ℤ) ^ n := Int.eq_of_mul_eq_mul_left hx0 h'
      exact three_pow_ne_five n heq.symm
  · intro n
    refine ⟨?_, ?_⟩
    · intro h
      have h7 : (7 : ℤ) ∣ (3 : ℤ) ^ n := ⟨x, by linarith⟩
      have h7N : (7 : ℕ) ∣ (3 : ℕ) ^ n := by exact_mod_cast h7
      have : 7 ∣ 3 := Nat.prime_seven.dvd_of_dvd_pow h7N
      omega
    · intro h
      have h' : x * 7 = x * (3 : ℤ) ^ n := by simpa [mul_comm] using h
      have heq : (7 : ℤ) = (3 : ℤ) ^ n := Int.eq_of_mul_eq_mul_left hx0 h'
      exact three_pow_ne_seven n heq.symm

/-- There is no θ-safe true root-releasing word beginning `(0,1,x)`, `x≥3`,
`x≡3 (mod 4)`, whose odd entries all lie on the two chains
`{3^n : n≥0} ∪ {x 3^n : n≥0}`. -/
theorem no_two_chain_only_prefix (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hpref : ∃ T : List ℤ, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0)
    (hodd : ∀ z ∈ Q, z % 2 = 1 →
      ∃ n : ℕ, z = (3 : ℤ) ^ n ∨ z = x * (3 : ℤ) ^ n) :
    False := by
  have hesc := (forced_escape_prefix θ Q x hx hxmod hS hpref hrel).2.2
  have hxodd : x % 2 = 1 := x_odd hxmod
  have h32odd : (3 * x - 2) % 2 = 1 := by omega
  have h5odd : (5 * x) % 2 = 1 := by omega
  have h7odd : (7 * x) % 2 = 1 := by omega
  have hSx := not_in_Sx_escape (x := x) hx
  rcases hesc with h32 | h5 | h7
  · obtain ⟨n, hn⟩ := hodd (3 * x - 2) h32 h32odd
    rcases hn with h | h
    · exact (hSx.1 n).1 h
    · exact (hSx.1 n).2 h
  · obtain ⟨n, hn⟩ := hodd (5 * x) h5 h5odd
    rcases hn with h | h
    · exact (hSx.2.1 n).1 h
    · exact (hSx.2.1 n).2 h
  · obtain ⟨n, hn⟩ := hodd (7 * x) h7 h7odd
    rcases hn with h | h
    · exact (hSx.2.2 n).1 h
    · exact (hSx.2.2 n).2 h


end Erdos195

theorem solution (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Erdos195.Safe (Erdos195.treeLt θ) Q)
    (hpref : ∃ T : List ℤ, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0)
    (hodd : ∀ z ∈ Q, z % 2 = 1 →
      ∃ n : ℕ, z = (3 : ℤ) ^ n ∨ z = x * (3 : ℤ) ^ n) :
    False :=
  Erdos195.no_two_chain_only_prefix θ Q x hx hxmod hS hpref hrel hodd
