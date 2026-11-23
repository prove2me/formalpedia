-- Prove2me | solution 1 for Formalism.HC.Der.Rd.weight_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:57.598277+00:00
-- url     : https://prove2.me/submissions/21fabe14-f4dc-4f47-a6f4-5bba2e3a4126

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_sum_totient_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
private theorem totient_ne_zero_of_ne_zero {n : ℕ} (hn : n ≠ 0) : n.totient ≠ 0 := by
  first
  | exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  | exact (Nat.totient_pos (Nat.pos_of_ne_zero hn)).ne'
  | simpa using hn
private theorem isPrimePow_of_dvd_isPrimePow_of_ne_one {n k : ℕ} (hn : IsPrimePow n) (hk : k ∣ n) (hk1 : k ≠ 1) :
    IsPrimePow k := by
  rw [isPrimePow_nat_iff] at hn ⊢
  obtain ⟨q, e, hq, he, rfl⟩ := hn
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hq).1 hk
  exact ⟨q, i, hq, Nat.pos_of_ne_zero (by rintro rfl; exact hk1 (pow_zero q)), rfl⟩
private theorem exists_eq_prime_pow_mul_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    ∃ v M : ℕ, ¬ p ∣ M ∧ n = p ^ v * M := by
  first
  | exact Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  | exact ⟨n.factorization p, n / p ^ n.factorization p, Nat.not_dvd_ordCompl hp hn,
      (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
private theorem prime_pow_dvd_prime_pow_iff_le {p a b : ℕ} (hp : p.Prime) : p ^ a ∣ p ^ b ↔ a ≤ b := by
  first
  | exact Nat.pow_dvd_pow_iff_le_right hp.one_lt
  | exact pow_dvd_pow_iff_le hp.ne_zero hp.not_isUnit
  | exact ⟨fun h => (Nat.pow_le_pow_iff_right hp.one_lt).mp (Nat.le_of_dvd (pow_pos hp.pos _) h),
      fun h => pow_dvd_pow p h⟩
variable {N : ℕ} [NeZero N]
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
namespace Formalism.HC.Der.Rd
theorem _root_.solution {N m : ℕ} (hN : N ≠ 0) (hm : m ∣ N) (hm1 : m ≠ 1) :
    ∑ m' ∈ N.divisors.filter (fun m' => m ∣ m'), vonMangoldt m' * ((N / m').totient : ℝ) =
      (N.totient : ℝ) * (vonMangoldt m / (m.totient : ℝ)) := by
  by_cases hpp : IsPrimePow m
  swap
  · rw [vonMangoldt_eq_zero_iff.mpr hpp, zero_div, mul_zero]
    refine Finset.sum_eq_zero fun m' hm' => ?_
    rw [Finset.mem_filter] at hm'
    have h0 : vonMangoldt m' = 0 :=
      vonMangoldt_eq_zero_iff.mpr fun h => hpp (isPrimePow_of_dvd_isPrimePow_of_ne_one h hm'.2 hm1)
    rw [h0, zero_mul]
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hex : ∃ v M : ℕ, ¬ p ∣ M ∧ N = p ^ v * M := exists_eq_prime_pow_mul_not_dvd hN hp
  obtain ⟨v, M, hpM, rfl⟩ := hex
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have hdvd : ∀ k, p ^ k ∣ p ^ v * M ↔ k ≤ v := fun k =>
    ⟨fun h => (prime_pow_dvd_prime_pow_iff_le hp).mp ((Nat.Coprime.pow_left k hcop).dvd_of_dvd_mul_right h),
      fun h => (pow_dvd_pow p h).mul_right M⟩
  have hjv : j ≤ v := (hdvd j).mp hm
  have hsub : (range (v - j + 1)).image (fun i => p ^ (j + i)) ⊆
      (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m') := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨(hdvd _).mpr (by omega), hN⟩, pow_dvd_pow p (by omega)⟩
  have hzero : ∀ x ∈ (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m'),
      x ∉ (range (v - j + 1)).image (fun i => p ^ (j + i)) →
        vonMangoldt x * (((p ^ v * M) / x).totient : ℝ) = 0 := by
    intro x hx hxT
    rw [Finset.mem_filter, Nat.mem_divisors] at hx
    by_contra hne
    have hx' : vonMangoldt x ≠ 0 := fun h => hne (by rw [h, zero_mul])
    rw [Ne, vonMangoldt_eq_zero_iff, not_not, isPrimePow_nat_iff] at hx'
    obtain ⟨q, k, hq, hk, rfl⟩ := hx'
    have hpq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow ((dvd_pow_self p hj.ne').trans hx.2))
    subst hpq
    have hjk : j ≤ k := (prime_pow_dvd_prime_pow_iff_le hp).mp hx.2
    have hkv : k ≤ v := (hdvd k).mp hx.1.1
    apply hxT
    rw [Finset.mem_image]
    exact ⟨k - j, Finset.mem_range.mpr (by omega), by congr 1; omega⟩
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_image (by
    intro a _ b _ h
    have h2 : j + a = j + b := Nat.pow_right_injective hp.two_le h
    omega)]
  have hterm : ∀ i ∈ range (v - j + 1), vonMangoldt (p ^ (j + i)) * (((p ^ v * M) / p ^ (j + i)).totient : ℝ) =
      Real.log p * (((p ^ (v - j - i)).totient * M.totient : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    have h1 : p ^ v * M = p ^ (j + i) * (p ^ (v - j - i) * M) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [h1, Nat.mul_div_cancel_left _ (pow_pos hp.pos _), Nat.totient_mul (Nat.Coprime.pow_left _ hcop)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : ∑ i ∈ range (v - j + 1), (p ^ (v - j - i)).totient * M.totient = p ^ (v - j) * M.totient := by
    rw [← Finset.sum_mul, ← sum_totient_pow hp (v - j)]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 2
    omega
  rw [← Nat.cast_sum, hsum]
  have hphi : (p ^ v).totient = p ^ (v - j) * (p ^ j).totient := by
    rw [Nat.totient_prime_pow hp (by omega), Nat.totient_prime_pow hp hj, ← mul_assoc, ← pow_add]
    congr 2
    omega
  have hpj : ((p ^ j).totient : ℝ) ≠ 0 := by
    exact_mod_cast totient_ne_zero_of_ne_zero (pow_ne_zero j hp.ne_zero)
  rw [vonMangoldt_apply_pow hj.ne', vonMangoldt_apply_prime hp,
    Nat.totient_mul (Nat.Coprime.pow_left v hcop), hphi]
  have e : ((p ^ j).totient : ℝ) * (Real.log p / ((p ^ j).totient : ℝ)) = Real.log p := by
    first
    | rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hpj, mul_one]
    | field_simp
  push_cast
  linear_combination (-((p : ℝ) ^ (v - j) * (M.totient : ℝ))) * e
end Formalism.HC.Der.Rd
