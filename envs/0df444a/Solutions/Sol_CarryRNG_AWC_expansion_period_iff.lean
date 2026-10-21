-- Prove2me | solution 1 for CarryRNG.AWC.expansion_period_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:54:58.847705+00:00
-- url     : https://prove2.me/submissions/0e0a4c1d-cf98-41ce-8ebf-ecdc4d5391b5

import Mathlib
import Definitions.Def_CarryRNG_AWC_digit

set_option autoImplicit false

namespace CarryRNG.AWC

lemma digit_rel (b m k j : ℕ) (hj : 1 ≤ j) :
    b * (b ^ (j - 1) * k % m) = m * digit b m k j + b ^ j * k % m := by
  unfold digit
  have h1 : b ^ j * k % m = b * (b ^ (j - 1) * k % m) % m := by
    have : b ^ j * k = b * (b ^ (j - 1) * k) := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp [pow_succ]; ring
    rw [this, Nat.mul_mod_mod]
  rw [h1]
  exact (Nat.div_add_mod _ _).symm

lemma expansion_period_iff' (b m k : ℕ) (hb : 2 ≤ b) (hm : 1 < m) (hk : k < m)
    (hkm : Nat.Coprime k m) (hbm : Nat.Coprime b m) (p : ℕ) (hp : 0 < p) :
    (∀ j, 1 ≤ j → digit b m k (j + p) = digit b m k j) ↔ orderOf (b : ZMod m) ∣ p := by
  rw [orderOf_dvd_iff_pow_eq_one]
  have hz : ((b : ZMod m)) ^ p = 1 ↔ b ^ p ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [hz]
  constructor
  · intro hper
    -- remainders
    set R : ℕ → ℤ := fun j => ((b ^ (j - 1) * k % m : ℕ) : ℤ) with hR
    have hrel : ∀ j, 1 ≤ j → (b : ℤ) * R j = m * digit b m k j + R (j + 1) := by
      intro j hj
      have := digit_rel b m k j hj
      simp only [hR]
      have e : j + 1 - 1 = j := by omega
      rw [e]
      exact_mod_cast this
    set Δ : ℕ → ℤ := fun j => R (j + p) - R j with hΔ
    have hstep : ∀ j, 1 ≤ j → Δ (j + 1) = b * Δ j := by
      intro j hj
      have h1 := hrel j hj
      have h2 := hrel (j + p) (by omega)
      have h3 := hper j hj
      simp only [hΔ]
      have e : j + p + 1 = j + 1 + p := by omega
      rw [e] at h2
      rw [h3] at h2
      linarith
    have hpow : ∀ n, Δ (1 + n) = (b : ℤ) ^ n * Δ 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := hstep (1 + n) (by omega)
        rw [show 1 + (n + 1) = 1 + n + 1 by omega, this, ih]
        ring
    have hbound : ∀ j, |Δ j| < m := by
      intro j
      have h1 : (0 : ℤ) ≤ R j := Int.natCast_nonneg _
      have h2 : (0 : ℤ) ≤ R (j + p) := Int.natCast_nonneg _
      have h3 : R j < m := by
        simp only [hR]; exact_mod_cast Nat.mod_lt _ (by omega)
      have h4 : R (j + p) < m := by
        simp only [hR]; exact_mod_cast Nat.mod_lt _ (by omega)
      rw [abs_lt]; simp only [hΔ]; constructor <;> linarith
    have hzero : Δ 1 = 0 := by
      by_contra hne
      have h1 := hbound (1 + m)
      rw [hpow, abs_mul, abs_pow, Nat.abs_cast] at h1
      have h2 : 1 ≤ |Δ 1| := Int.one_le_abs hne
      have h3 : (m : ℤ) < (b : ℤ) ^ m := by
        have : m < b ^ m := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hb m)
        exact_mod_cast this
      nlinarith
    have : R (1 + p) = R 1 := by
      have := hzero; simp only [hΔ] at this; linarith
    have h5 : b ^ p * k % m = k % m := by
      have h := this
      simp only [hR, Nat.add_sub_cancel_left, Nat.sub_self, pow_zero, one_mul] at h
      exact_mod_cast h
    have h6 : b ^ p * k ≡ 1 * k [MOD m] := by
      show b ^ p * k % m = 1 * k % m
      rw [one_mul]; exact h5
    exact Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hkm) h6
  · intro hmod j hj
    unfold digit
    have e : j + p - 1 = (j - 1) + p := by omega
    rw [e]
    have : b ^ (j - 1 + p) * k ≡ b ^ (j - 1) * k [MOD m] := by
      have h1 : b ^ (j - 1) * b ^ p * k = b ^ (j - 1) * k * b ^ p := by ring
      have h2 : b ^ (j - 1 + p) * k = b ^ (j - 1) * k * b ^ p := by rw [pow_add]; ring
      rw [h2]
      calc b ^ (j - 1) * k * b ^ p ≡ b ^ (j - 1) * k * 1 [MOD m] := Nat.ModEq.mul_left _ hmod
        _ = b ^ (j - 1) * k := by ring
    rw [this]

end CarryRNG.AWC

theorem solution (b m k : ℕ) (hb : 2 ≤ b) (hm : 1 < m) (hk : k < m)
    (hkm : Nat.Coprime k m) (hbm : Nat.Coprime b m) (p : ℕ) (hp : 0 < p) :
    (∀ j, 1 ≤ j → CarryRNG.AWC.digit b m k (j + p) = CarryRNG.AWC.digit b m k j) ↔
      orderOf (b : ZMod m) ∣ p :=
  CarryRNG.AWC.expansion_period_iff' b m k hb hm hk hkm hbm p hp
