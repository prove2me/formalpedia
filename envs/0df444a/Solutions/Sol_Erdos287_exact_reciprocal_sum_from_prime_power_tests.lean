-- Prove2me | solution 1 for Erdos287.exact_reciprocal_sum_from_prime_power_tests
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:06:26.578964+00:00
-- url     : https://prove2.me/submissions/bcf953a7-1ae1-4b1b-b186-3e56cbe78596

import Mathlib

open Finset

set_option autoImplicit false

/-- Prime-power tests determine exact unit reciprocal mass within one step of
the rational grid left by the unchecked factors of the common denominator. -/
theorem solution (D : Finset ℕ) (C W : ℕ) (hC : 0 < C)
    (hpos : ∀ n ∈ D, 0 < n) (hdiv : ∀ n ∈ D, n ∣ C)
    (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hpow : ∀ p ∈ P, p ^ e p ∣ C)
    (hwidth : C / (∏ p ∈ P, p ^ e p) ≤ W)
    (hlo : (1 : ℚ) ≤ ∑ n ∈ D, (1 : ℚ) / n)
    (hhi : (∑ n ∈ D, (1 : ℚ) / n) < 1 + (1 : ℚ) / W) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔
      ∀ p ∈ P, p ^ e p ∣ ∑ n ∈ D.filter (fun n => ¬ p ^ e p ∣ C / n), C / n := by
  let N := ∑ n ∈ D, C / n
  let A := ∏ p ∈ P, p ^ e p
  let R := C / A
  let s := ∑ n ∈ D, (1 : ℚ) / n
  change s = 1 ↔ _
  have hscaled : (C : ℚ) * s = N := by
    simp only [s, N, mul_sum, Nat.cast_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [mul_one_div]
    apply (div_eq_iff (Nat.cast_ne_zero.mpr (hpos n hn).ne')).mpr
    exact_mod_cast (Nat.div_mul_cancel (hdiv n hn)).symm
  have hcongr (p : ℕ) : (p ^ e p ∣ ∑ n ∈ D.filter (fun n => ¬ p ^ e p ∣ C / n), C / n) ↔
      p ^ e p ∣ N := by
    let K := D.filter (fun n => ¬ p ^ e p ∣ C / n)
    let J := D.filter (fun n => ¬ ¬ p ^ e p ∣ C / n)
    have hj : p ^ e p ∣ ∑ n ∈ J, C / n :=
      dvd_sum fun _ h => not_not.mp (mem_filter.mp h).2
    have hsplit : (∑ n ∈ K, C / n) + (∑ n ∈ J, C / n) = N :=
      sum_filter_add_sum_filter_not D (fun n => ¬ p ^ e p ∣ C / n) (fun n => C / n)
    change p ^ e p ∣ (∑ n ∈ K, C / n) ↔ _
    constructor
    · intro h
      rw [← hsplit]
      exact dvd_add h hj
    · intro h
      have heq : N - (∑ n ∈ J, C / n) = ∑ n ∈ K, C / n := by omega
      rw [← heq]
      exact Nat.dvd_sub h hj
  constructor
  · intro hs p hp
    apply (hcongr p).2
    rw [hs, mul_one] at hscaled
    have hNC : C = N := by exact_mod_cast hscaled
    exact hNC ▸ hpow p hp
  · intro hs
    have hproduct (n : ℕ) (hn : ∀ p ∈ P, p ^ e p ∣ n) : A ∣ n := by
      apply Int.natCast_dvd_natCast.mp
      rw [show A = ∏ p ∈ P, p ^ e p from rfl, Nat.cast_prod]
      refine Finset.prod_dvd_of_coprime ?_ fun p hp => Int.natCast_dvd_natCast.mpr (hn p hp)
      intro p hp q hq hpq
      exact Nat.isCoprime_iff_coprime.mpr
        ((((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq).pow_left (e p)).pow_right (e q))
    have hAC : A ∣ C := hproduct C hpow
    have hApos : 0 < A := prod_pos fun p hp => pow_pos (hP p hp).pos _
    have hRpos : 0 < R := Nat.div_pos (Nat.le_of_dvd hC hAC) hApos
    have hRcast : (0 : ℚ) < R := by exact_mod_cast hRpos
    have hAcast : (0 : ℚ) < A := by exact_mod_cast hApos
    have hRW : (R : ℚ) ≤ W := by exact_mod_cast hwidth
    have hCeq : (R : ℚ) * A = C := by exact_mod_cast Nat.div_mul_cancel hAC
    obtain ⟨K, hK⟩ := hproduct N fun p hp => (hcongr p).1 (hs p hp)
    have hKcast : (N : ℚ) = (A : ℚ) * K := by exact_mod_cast hK
    have hsK : s = (K : ℚ) / R := by
      apply (eq_div_iff hRcast.ne').mpr
      apply mul_right_cancel₀ hAcast.ne'
      calc
        s * (R : ℚ) * A = (C : ℚ) * s := by rw [← hCeq]; ring
        _ = N := hscaled
        _ = (K : ℚ) * A := hKcast.trans (mul_comm _ _)
    change 1 ≤ s at hlo
    change s < 1 + (1 : ℚ) / W at hhi
    rw [hsK] at hlo hhi
    have hloK : (R : ℚ) ≤ K := by
      simpa only [one_mul] using (le_div_iff₀ hRcast).mp hlo
    have hu : (K : ℚ) / R < 1 + (1 : ℚ) / R :=
      hhi.trans_le (add_le_add le_rfl (one_div_le_one_div_of_le hRcast hRW))
    have huK := (div_lt_iff₀ hRcast).mp hu
    rw [add_mul, one_mul, div_mul_cancel₀ (1 : ℚ) hRcast.ne'] at huK
    have hlowNat : R ≤ K := by exact_mod_cast hloK
    have hupNat : K < R + 1 := by exact_mod_cast huK
    have hEq : K = R := by omega
    rw [hsK, hEq, div_self hRcast.ne']

