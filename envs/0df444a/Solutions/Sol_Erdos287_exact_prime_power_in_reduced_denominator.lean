-- Prove2me | solution 1 for Erdos287.exact_prime_power_in_reduced_denominator
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:14:24.644797+00:00
-- url     : https://prove2.me/submissions/84616967-f2db-4525-bd3a-3cdc2b227700

import Mathlib

open Finset

set_option autoImplicit false

private theorem norm_power_iff_den {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (x : ℚ) :
    padicNorm p x = (p : ℚ) ^ e ↔ padicValNat p x.den = e := by
  have hp : p.Prime := Fact.out
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℚ) < p := by positivity
  have hnum (hd : 0 < padicValNat p x.den) : padicValInt p x.num = 0 := by
    have hdiv : p ∣ x.den := by
      simpa only [pow_one] using (padicValNat_dvd_iff_le (n := 1) x.den_ne_zero).mpr hd
    apply padicValInt.eq_zero_of_not_dvd
    intro hn
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Int.natCast_dvd.mp hn) hdiv) x.reduced
  constructor
  · intro h
    have hx : x ≠ 0 := by
      intro hz
      rw [hz, padicNorm.zero] at h
      exact (pow_ne_zero e hpp.ne') h.symm
    rw [padicNorm.eq_zpow_of_nonzero hx, ← zpow_natCast, zpow_right_inj₀ hpp hpq.ne',
      padicValRat_def] at h
    have hd : 0 < padicValNat p x.den := by omega
    rw [hnum hd] at h
    omega
  · intro h
    have hx : x ≠ 0 := by
      intro hz
      have hone : padicValNat p 1 = 0 := padicValNat.eq_zero_of_not_dvd hp.not_dvd_one
      simp [hz, hone] at h
      omega
    have hn := hnum (by omega)
    rw [padicNorm.eq_zpow_of_nonzero hx, padicValRat_def, hn, h]
    simp only [Nat.cast_zero, zero_sub, neg_neg, zpow_natCast]

/-- The leading cofactor sum determines whether the full prime power survives
in the reduced denominator of a sum with integer weights. -/
theorem solution (D : Finset ℕ) (w : ℕ → ℤ) (p e L : ℕ)
    (hp : p.Prime) (he : 1 ≤ e) (hL : ¬ p ∣ L)
    (hpos : ∀ n ∈ D, 0 < n) (hmax : ∀ n ∈ D, padicValNat p n ≤ e)
    (hcof : ∀ n ∈ D, padicValNat p n = e → n / p ^ e ∣ L) :
    padicValNat p (∑ n ∈ D, (w n : ℚ) / n).den = e ↔
      ¬ (p : ℤ) ∣ ∑ n ∈ D.filter (fun n => padicValNat p n = e),
        w n * ((L / (n / p ^ e) : ℕ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  let H := D.filter (fun n => padicValNat p n = e)
  let K := D.filter (fun n => padicValNat p n ≠ e)
  let U : ℚ := ∑ n ∈ H, (w n : ℚ) / n
  let V : ℚ := ∑ n ∈ K, (w n : ℚ) / n
  let A : ℤ := ∑ n ∈ H, w n * ((L / (n / p ^ e) : ℕ) : ℤ)
  have hpp : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hLpos : 0 < L := Nat.pos_of_ne_zero fun hz => hL (by rw [hz]; exact dvd_zero p)
  have hLq : (0 : ℚ) < L := by exact_mod_cast hLpos
  have hdenom : (0 : ℚ) < (p : ℚ) ^ e * L := mul_pos (pow_pos hpp e) hLq
  have hU : U = (A : ℚ) / ((p : ℚ) ^ e * L) := by
    simp only [U, A, Int.cast_sum, Int.cast_mul, Int.cast_natCast, sum_div]
    refine sum_congr rfl fun n hn => ?_
    have ⟨hnD, hv⟩ := mem_filter.mp hn
    have hdvd : p ^ e ∣ n := (padicValNat_dvd_iff_le (hpos n hnD).ne').mpr hv.ge
    have hnq : (0 : ℚ) < n := by exact_mod_cast hpos n hnD
    have hn_eq : ((n / p ^ e : ℕ) : ℚ) * (p : ℚ) ^ e = n := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hLc : ((L / (n / p ^ e) : ℕ) : ℚ) * ((n / p ^ e : ℕ) : ℚ) = L := by
      exact_mod_cast Nat.div_mul_cancel (hcof n hnD hv)
    have hx : (1 : ℚ) / n = ((L / (n / p ^ e) : ℕ) : ℚ) / ((p : ℚ) ^ e * L) := by
      apply (div_eq_div_iff hnq.ne' hdenom.ne').mpr
      rw [one_mul, ← hn_eq, ← mul_assoc, hLc, mul_comm]
    rw [← mul_one_div, hx, mul_div_assoc]
  have hV : padicNorm p V ≤ (p : ℚ) ^ (e - 1) := by
    apply padicNorm.sum_le' _ (by positivity)
    intro n hn
    have ⟨hnD, hv⟩ := mem_filter.mp hn
    have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hpos n hnD).ne'
    have hrecip : padicNorm p ((1 : ℚ) / n) = (p : ℚ) ^ padicValNat p n := by
      rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hnq), padicValRat.inv,
        padicValRat.of_nat, neg_neg, zpow_natCast]
    rw [← mul_one_div, padicNorm.mul, hrecip]
    calc
      _ ≤ 1 * (p : ℚ) ^ padicValNat p n :=
        mul_le_mul_of_nonneg_right (padicNorm.of_int _) (by positivity)
      _ ≤ _ := by
        rw [one_mul]
        have hbound := hmax n hnD
        exact pow_le_pow_right₀ hpq.le (by omega)
  have hnP : padicNorm p ((p : ℚ) ^ e) = ((p : ℚ) ^ e)⁻¹ := by
    have hpne : ((p ^ e : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero e hp.ne_zero)
    rw [← Nat.cast_pow, padicNorm.eq_zpow_of_nonzero hpne,
      padicValRat.of_nat, padicValNat.prime_pow, zpow_neg, zpow_natCast, Nat.cast_pow]
  have hnU : padicNorm p U = padicNorm p (A : ℚ) * (p : ℚ) ^ e := by
    rw [hU, padicNorm.div, padicNorm.mul, hnP, (padicNorm.nat_eq_one_iff L).mpr hL,
      mul_one, div_inv_eq_mul]
  have hsmall : (p : ℚ) ^ (e - 1) < (p : ℚ) ^ e :=
    pow_lt_pow_right₀ hpq (by omega)
  have hsum : U + V = ∑ n ∈ D, (w n : ℚ) / n :=
    sum_filter_add_sum_filter_not D (fun n => padicValNat p n = e) (fun n => (w n : ℚ) / n)
  rw [← hsum, ← norm_power_iff_den he]
  change padicNorm p (U + V) = (p : ℚ) ^ e ↔ ¬ (p : ℤ) ∣ A
  constructor
  · intro hs hd
    have hA : padicNorm p (A : ℚ) ≤ (p : ℚ)⁻¹ := by
      have hh := (padicNorm.dvd_iff_norm_le (p := p) (n := 1) (z := A)).mp (by simpa using hd)
      simpa only [Nat.cast_one, zpow_neg, zpow_one] using hh
    have hV' : padicNorm p V < (p : ℚ) ^ e := hV.trans_lt hsmall
    have hU' : padicNorm p U ≤ (p : ℚ) ^ (e - 1) := by
      rw [hnU]
      calc
        _ ≤ (p : ℚ)⁻¹ * (p : ℚ) ^ e := mul_le_mul_of_nonneg_right hA (by positivity)
        _ = (p : ℚ) ^ (e - 1) := by
          rw [show (p : ℚ) ^ e = (p : ℚ) ^ (e - 1) * p by rw [← pow_succ, Nat.sub_add_cancel he]]
          field_simp
    have hbound : padicNorm p (U + V) < (p : ℚ) ^ e :=
      padicNorm.nonarchimedean.trans_lt (max_lt (hU'.trans_lt hsmall) hV')
    exact hbound.ne hs
  · intro hA
    rw [(padicNorm.int_eq_one_iff A).mpr hA, one_mul] at hnU
    have hlt : padicNorm p V < padicNorm p U := by rw [hnU]; exact hV.trans_lt hsmall
    rw [padicNorm.add_eq_max_of_ne hlt.ne', max_eq_left hlt.le, hnU]

