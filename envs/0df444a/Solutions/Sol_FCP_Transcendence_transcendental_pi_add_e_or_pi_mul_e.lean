-- Prove2me | solution 1 for FCP.Transcendence.transcendental_pi_add_e_or_pi_mul_e
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T11:56:26.082691+00:00
-- url     : https://prove2.me/submissions/ab008cc6-4d5d-4e75-8709-7e9c2ccfd251

import Mathlib

open Real
open Polynomial Filter Topology
open scoped BigOperators

namespace P2M

theorem root_polynomial (s : Finset ℕ) (hs : ∀ j ∈ s, j ≠ 0) :
    ∃ f : ℤ[X], f.eval 0 ≠ 0 ∧ ∀ j ∈ s, (j : ℂ) ∈ f.aroots ℂ := by
  let f : ℤ[X] := ∏ j ∈ s, (X - C (j : ℤ))
  have hf : f.eval 0 ≠ 0 := by
    dsimp [f]
    simp only [eval_prod, eval_sub, eval_X, eval_C, zero_sub]
    exact Finset.prod_ne_zero_iff.mpr (fun j hj => neg_ne_zero.mpr (by exact_mod_cast hs j hj))
  refine ⟨f, hf, ?_⟩
  intro j hj
  rw [mem_aroots]
  refine ⟨fun h => hf (by simp [h]), ?_⟩
  simp only [f, map_prod]
  apply Finset.prod_eq_zero hj
  simp

theorem exponential_relation (q : ℤ[X]) (h0 : q.coeff 0 ≠ 0)
    (hq : aeval (Complex.exp 1) q = 0) :
    (q.coeff 0 : ℂ) + ∑ j ∈ q.support.erase 0,
      (q.coeff j : ℂ) * Complex.exp (j : ℂ) = 0 := by
  have hz : 0 ∈ q.support := mem_support_iff.mpr h0
  have hsum := Finset.sum_erase_add q.support
    (fun j => (q.coeff j : ℂ) * Complex.exp (j : ℂ)) hz
  have heval : ∑ j ∈ q.support, (q.coeff j : ℂ) * Complex.exp (j : ℂ) = 0 := by
    simpa [aeval_def, eval₂_eq_sum, Polynomial.sum, ← Complex.exp_nat_mul, mul_one] using hq
  simpa [add_comm] using hsum.trans heval

theorem no_exponential_relation (s : Finset ℕ) (hs : ∀ j ∈ s, j ≠ 0)
    (a : ℕ → ℤ) (h0 : a 0 ≠ 0)
    (hrel : (a 0 : ℂ) + ∑ j ∈ s, (a j : ℂ) * Complex.exp (j : ℂ) = 0) : False := by
  obtain ⟨f, hf, hroots⟩ := root_polynomial s hs
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf
  let A : ℝ := ∑ j ∈ s, ‖(a j : ℂ)‖
  have ht := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop A c 1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N (max (f.eval 0).natAbs (a 0).natAbs + 1))
  have hpf : (f.eval 0).natAbs < p := by omega
  have hpa : (a 0).natAbs < p := by omega
  have hpN : N ≤ p := by omega
  obtain ⟨n, hpn, g, _, hg⟩ := hc p hpf hprime
  let J : ℤ := n * a 0 + p * ∑ j ∈ s, a j * g.eval (j : ℤ)
  have hpa0 : ¬ (p : ℤ) ∣ a 0 := by
    intro hd
    have hd' : p ∣ (a 0).natAbs := Int.natCast_dvd.mp hd
    exact (not_le.mpr hpa) (Nat.le_of_dvd (Int.natAbs_pos.mpr h0) hd')
  have hJ : J ≠ 0 := by
    intro heq
    have hd : (p : ℤ) ∣ n * a 0 := by
      have hdJ : (p : ℤ) ∣ J := heq ▸ dvd_zero _
      exact (dvd_add_left (dvd_mul_right _ _)).mp hdJ
    have hd' := Int.natCast_dvd.mp hd
    rw [Int.natAbs_mul] at hd'
    rcases hprime.dvd_mul.mp hd' with hn | ha
    · exact hpn (Int.natCast_dvd.mpr hn)
    · exact hpa0 (Int.natCast_dvd.mpr ha)
  have hJlow : 1 ≤ ‖(J : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have hpos : (0 : ℤ) < |J| := abs_pos.mpr hJ
    have hle : (1 : ℤ) ≤ |J| := by omega
    exact_mod_cast hle
  have hident : (J : ℂ) = -(∑ j ∈ s, (a j : ℂ) *
      (n * Complex.exp (j : ℂ) - p * aeval (j : ℂ) g)) := by
    have hv (j : ℕ) : aeval (j : ℂ) g = (↑(g.eval (j : ℤ)) : ℂ) := by
      simpa using (aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (j : ℤ) g)
    have factor_sum (k : ℂ) (u : ℕ → ℂ) :
        (∑ j ∈ s, (a j : ℂ) * (k * u j)) =
          k * ∑ j ∈ s, (a j : ℂ) * u j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hcast : (J : ℂ) = (n : ℂ) * (a 0 : ℂ) +
        (p : ℂ) * ∑ j ∈ s, (a j : ℂ) * (↑(g.eval (j : ℤ)) : ℂ) := by
      simp only [J, Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    rw [hcast]
    simp_rw [hv, mul_sub, Finset.sum_sub_distrib]
    rw [factor_sum, factor_sum]
    have hmul := congrArg (fun z : ℂ => (n : ℂ) * z) hrel
    linear_combination hmul
  have hbound : ‖(J : ℂ)‖ ≤ A * c ^ p / (p - 1).factorial := by
    rw [hident, norm_neg]
    calc
      _ ≤ ∑ j ∈ s, ‖(a j : ℂ) * (n * Complex.exp (j : ℂ) - p * aeval (j : ℂ) g)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s, ‖(a j : ℂ)‖ * (c ^ p / (p - 1).factorial) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [zsmul_eq_mul, nsmul_eq_mul] using hg (hroots j hj)
      _ = A * c ^ p / (p - 1).factorial := by rw [← Finset.sum_mul]; dsimp [A]; ring
  exact (not_lt_of_ge (hJlow.trans hbound)) (hN p hpN)

theorem transcendental_exp_one_complex : Transcendental ℚ (Complex.exp 1) := by
  intro h
  have hi : IsAlgebraic ℤ (Complex.exp 1) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr h
  obtain ⟨q, h0, hq⟩ := hi.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_iff_ne_zero.mpr (Complex.exp_ne_zero 1))
  exact no_exponential_relation (q.support.erase 0)
    (fun j hj => (Finset.mem_erase.mp hj).1) q.coeff h0 (exponential_relation q h0 hq)

theorem transcendental_exp_one_real : Transcendental ℚ (Real.exp 1) := by
  intro h
  apply transcendental_exp_one_complex
  have hc : IsAlgebraic ℚ (algebraMap ℝ ℂ (Real.exp 1)) := h.algebraMap
  simpa using hc

theorem transcendental_sum_or_product {a b : ℝ} (ha : Transcendental ℚ a) :
    Transcendental ℚ (a + b) ∨ Transcendental ℚ (a * b) := by
  classical
  by_contra h
  have hs : IsAlgebraic ℚ (a + b) := Classical.not_not.mp (not_or.mp h).1
  have hp : IsAlgebraic ℚ (a * b) := Classical.not_not.mp (not_or.mp h).2
  have heq : (a + b) ^ 2 - (4 : ℚ) • (a * b) = (a - b) ^ 2 := by
    norm_num [Algebra.smul_def]
    ring
  have hd2 : IsAlgebraic ℚ ((a - b) ^ 2) := by
    rw [← heq]
    exact (hs.pow 2).sub (hp.smul (4 : ℚ))
  have hd : IsAlgebraic ℚ (a - b) := IsAlgebraic.of_pow (by decide : 0 < (2 : ℕ)) hd2
  have heq2 : (1 / 2 : ℚ) • ((a + b) + (a - b)) = a := by
    norm_num [Algebra.smul_def]
    ring
  apply ha
  rw [← heq2]
  exact (hs.add hd).smul (1 / 2 : ℚ)

end P2M

theorem solution :
    Transcendental ℚ (π + exp 1) ∨ Transcendental ℚ (π * exp 1) := by
  simpa [add_comm, mul_comm] using
    (P2M.transcendental_sum_or_product (b := Real.pi) P2M.transcendental_exp_one_real)
