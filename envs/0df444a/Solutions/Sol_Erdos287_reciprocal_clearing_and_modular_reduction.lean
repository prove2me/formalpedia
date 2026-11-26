-- Prove2me | solution 1 for Erdos287.reciprocal_clearing_and_modular_reduction
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:52:12.26193+00:00
-- url     : https://prove2.me/submissions/b7498c05-1868-43a4-bc4f-7c1be6814dac

import Mathlib

open Finset

set_option autoImplicit false

/-- Clearing positive denominators is compatible with reduction modulo any
modulus coprime to their common multiple. -/
theorem solution (D : Finset ℕ) (q L : ℕ) (hL : 0 < L) (hcop : L.Coprime q)
    (hdiv : ∀ n ∈ D, n ∣ L) :
    ((∑ n ∈ D, (1 : ℚ) / n) = 1 ↔ (∑ n ∈ D, L / n) = L) ∧
    ((∑ n ∈ D, (n : ZMod q)⁻¹) = 1 ↔ (∑ n ∈ D, L / n) ≡ L [MOD q]) := by
  let W := ∑ n ∈ D, L / n
  have hrat : (W : ℚ) = (L : ℚ) * (∑ n ∈ D, (1 : ℚ) / n) := by
    rw [mul_sum, show W = ∑ n ∈ D, L / n from rfl, Nat.cast_sum]
    apply sum_congr rfl
    intro n hn
    have hnz := (Nat.pos_of_dvd_of_pos (hdiv n hn) hL).ne'
    rw [mul_one_div]
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hnz)).mpr
    exact_mod_cast Nat.div_mul_cancel (hdiv n hn)
  have hLunit : IsUnit (L : ZMod q) := (ZMod.isUnit_iff_coprime L q).mpr hcop
  have hscaled : (L : ZMod q) * (∑ n ∈ D, (n : ZMod q)⁻¹) = W := by
    rw [mul_sum, show W = ∑ n ∈ D, L / n from rfl, Nat.cast_sum]
    apply sum_congr rfl
    intro n hn
    have hu : IsUnit (n : ZMod q) :=
      (ZMod.isUnit_iff_coprime n q).mpr (hcop.coprime_dvd_left (hdiv n hn))
    have hd : ((L / n : ℕ) : ZMod q) * n = (L : ZMod q) := by
      simpa only [Nat.cast_mul] using
        congrArg (fun k : ℕ => (k : ZMod q)) (Nat.div_mul_cancel (hdiv n hn))
    calc
      _ = ((L / n : ℕ) : ZMod q) * n * (n : ZMod q)⁻¹ := by rw [hd]
      _ = _ := by rw [mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]
  constructor
  · change (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔ W = L
    constructor
    · intro h
      rw [h, mul_one] at hrat
      exact_mod_cast hrat
    · intro h
      have he : (L : ℚ) * (∑ n ∈ D, (1 : ℚ) / n) = L * 1 := by
        rw [← hrat, h, mul_one]
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hL.ne') he
  · change (∑ n ∈ D, (n : ZMod q)⁻¹) = 1 ↔ W ≡ L [MOD q]
    rw [← ZMod.natCast_eq_natCast_iff W L q]
    constructor
    · intro h
      rw [h, mul_one] at hscaled
      exact hscaled.symm
    · intro h
      have he := congrArg (fun z : ZMod q => (L : ZMod q)⁻¹ * z) (hscaled.trans h)
      simpa only [← mul_assoc, ZMod.inv_mul_of_unit _ hLunit, one_mul] using he

