-- Prove2me | solution 1 for Erdos287.prime_layer_denominator_coprime_iff_inverse_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:37:23.352318+00:00
-- url     : https://prove2.me/submissions/6dfb513c-a151-4dc2-8a54-e57bddd717a4

import Mathlib

open Finset

set_option autoImplicit false

/-- At an exponent-one prime layer, zero cofactor inverse sum is exactly
the condition for removing the prime from its reduced denominator. -/
theorem solution (C : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hC : ∀ c ∈ C, 0 < c ∧ ¬ p ∣ c) :
    ¬ p ∣ (∑ c ∈ C, (1 : ℚ) / (p * c : ℕ)).den ↔
      (∑ c ∈ C, (c : ZMod p)⁻¹) = 0 := by
  let L := C.lcm id
  let W := ∑ c ∈ C, L / c
  let x := ∑ c ∈ C, (1 : ℚ) / (p * c : ℕ)
  change ¬ p ∣ x.den ↔ _
  have hL : ¬ p ∣ L := by
    intro h
    obtain ⟨c, hc, hd⟩ := (hp.prime.dvd_finsetProd_iff id).mp (h.trans (C.lcm_dvd_prod id))
    exact (hC c hc).2 hd
  have hL0 : L ≠ 0 := fun he => hL (he ▸ dvd_zero p)
  have hLq : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hL0
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hLunit : IsUnit (L : ZMod p) :=
    (ZMod.isUnit_iff_coprime L p).mpr (hp.coprime_iff_not_dvd.mpr hL).symm
  have hcast : (L : ZMod p) * (∑ c ∈ C, (c : ZMod p)⁻¹) = (W : ZMod p) := by
    rw [mul_sum, show W = ∑ c ∈ C, L / c from rfl, Nat.cast_sum]
    apply sum_congr rfl
    intro c hc
    have hu : IsUnit (c : ZMod p) :=
      (ZMod.isUnit_iff_coprime c p).mpr (hp.coprime_iff_not_dvd.mpr (hC c hc).2).symm
    have hd : ((L / c : ℕ) : ZMod p) * c = (L : ZMod p) := by
      simpa only [Nat.cast_mul] using
        congrArg (fun n : ℕ => (n : ZMod p)) (Nat.div_mul_cancel (show c ∣ L from dvd_lcm hc))
    rw [← hd, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]
  have hmod : (∑ c ∈ C, (c : ZMod p)⁻¹) = 0 ↔ p ∣ W := by
    rw [← ZMod.natCast_eq_zero_iff W p, ← hcast]
    exact ⟨fun h => by rw [h, mul_zero], fun h => hLunit.mul_left_cancel (h.trans (mul_zero _).symm)⟩
  have hx : x = (W : ℚ) / ((p : ℚ) * L) := by
    change x = ((∑ c ∈ C, L / c : ℕ) : ℚ) / ((p : ℚ) * L)
    rw [Nat.cast_sum, sum_div]
    refine sum_congr rfl fun c hc => ?_
    rw [Nat.cast_mul]
    have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hC c hc).1.ne'
    have he : ((L / c : ℕ) : ℚ) * c = L := by exact_mod_cast Nat.div_mul_cancel (dvd_lcm hc)
    apply (div_eq_div_iff (mul_ne_zero hpq hcq) (mul_ne_zero hpq hLq)).mpr
    rw [one_mul, mul_left_comm, he]
  rw [hmod]
  constructor
  · intro hden
    have hEq : (W : ℚ) / ((p : ℚ) * L) = (x.num : ℚ) / x.den := hx.symm.trans x.num_div_den.symm
    have he := (div_eq_div_iff (mul_ne_zero hpq hLq) (Nat.cast_ne_zero.mpr x.den_ne_zero)).mp hEq
    have he' : (W : ℤ) * x.den = x.num * ((p : ℤ) * L) := by exact_mod_cast he
    have hd : (p : ℤ) ∣ (W : ℤ) * x.den := by
      rw [he', ← mul_assoc, mul_comm x.num, mul_assoc]
      exact dvd_mul_right (p : ℤ) _
    have hd' : p ∣ W * x.den := Int.natCast_dvd_natCast.mp (by simpa only [Nat.cast_mul] using hd)
    exact (hp.dvd_mul.mp hd').resolve_right hden
  · intro hd
    have he : ((W / p : ℕ) : ℚ) * p = (W : ℚ) := by exact_mod_cast Nat.div_mul_cancel hd
    have hrepr : x = ((W / p : ℕ) : ℚ) / L := by
      rw [hx]
      apply (div_eq_div_iff (mul_ne_zero hpq hLq) hLq).mpr
      rw [← mul_assoc, he]
    have hint : x = Rat.divInt (↑(W / p : ℕ)) (↑L) := by
      rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
      exact hrepr
    have hden : x.den ∣ L := by
      rw [hint]
      exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)
    exact fun hpden => hL (hpden.trans hden)

