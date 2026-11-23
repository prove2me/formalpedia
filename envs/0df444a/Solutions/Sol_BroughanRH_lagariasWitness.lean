-- Prove2me | solution 1 for BroughanRH.lagariasWitness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:52:03.230405+00:00
-- url     : https://prove2.me/submissions/0ce8b96d-1e32-4466-9006-6b1de3f38b89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_lagarias
import Mathlib

open Finset

namespace BRHLagW

lemma log_ratio_ge (y : ℝ) (hy : 2 ≤ y) :
    2 / y ≤ Real.log (y + 1) - Real.log (y - 1) := by
  have hy0 : 0 < y := by linarith
  have hx : |1 / y| < 1 := by
    rw [abs_of_pos (by positivity)]; rw [div_lt_one hy0]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hx
  have h0 := le_hasSum hs 0 (fun j _ => by positivity)
  have e1 : Real.log (1 + 1 / y) = Real.log (y + 1) - Real.log y := by
    rw [← Real.log_div (by linarith) hy0.ne']; congr 1; field_simp
  have e2 : Real.log (1 - 1 / y) = Real.log (y - 1) - Real.log y := by
    rw [← Real.log_div (by linarith) hy0.ne']; congr 1; field_simp
  rw [e1, e2] at h0
  have : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / y) ^ (2 * 0 + 1) = 2 / y := by
    simp; ring
  linarith

lemma harmonic_le_log_sub (n m : ℕ) (hm : 0 < m) :
    (harmonic n : ℝ) ≤
      Real.log (∏ i ∈ Icc 1 n, ((2 * m * i + 1 : ℝ)) ^ m) -
        Real.log (∏ i ∈ Icc 1 n, ((2 * m * i - 1 : ℝ)) ^ m) := by
  have hpos : ∀ i ∈ Icc 1 n, (1 : ℝ) ≤ 2 * m * i - 1 := by
    intro i hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.1 hi).1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  rw [Real.log_prod (fun i hi => by have := hpos i hi; positivity),
    Real.log_prod (fun i hi => by have := hpos i hi; positivity), ← sum_sub_distrib,
    harmonic_eq_sum_Icc]
  push_cast
  apply sum_le_sum
  intro i hi
  rw [Real.log_pow, Real.log_pow]
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.1 hi).1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (2 : ℝ) ≤ 2 * m * i := by nlinarith
  have := log_ratio_ge (2 * m * i) h2
  have key : (m : ℝ) * (2 / (2 * m * i)) = (i : ℝ)⁻¹ := by field_simp
  calc (i : ℝ)⁻¹ = (m : ℝ) * (2 / (2 * m * i)) := key.symm
    _ ≤ m * (Real.log (2 * m * i + 1) - Real.log (2 * m * i - 1)) := by gcongr
    _ = _ := by ring

end BRHLagW

open BRHLagW in
theorem solution :
    ¬ ∃ n m k p q a b : ℕ, 0 < n ∧ 0 < m ∧ 0 < k ∧ 0 < p ∧ 0 < q ∧ 0 < a ∧ 0 < b ∧
      let c := ArithmeticFunction.sigma 1 n
      let s := ∏ i ∈ Finset.Icc 1 n, (2*m*i+1)^m
      let t := ∏ i ∈ Finset.Icc 1 n, (2*m*i-1)^m
      k^k * p^s * s^t + b = (c*t+k)^k * q^s * t^t ∧
        k^k * q^k * s + a = (k*q+p)^k * t := by
  rintro ⟨n, m, k, p, q, a, b, hn, hm, hk, hp, hq, ha, hb, h1, h2⟩
  set c := ArithmeticFunction.sigma 1 n with hc
  set s := ∏ i ∈ Finset.Icc 1 n, (2*m*i+1)^m with hs
  set t := ∏ i ∈ Finset.Icc 1 n, (2*m*i-1)^m with ht
  -- real versions
  set H : ℝ := (harmonic n : ℝ) with hH
  have hS : (s : ℝ) = ∏ i ∈ Icc 1 n, ((2 * m * i + 1 : ℝ)) ^ m := by rw [hs]; push_cast; rfl
  have hT : (t : ℝ) = ∏ i ∈ Icc 1 n, ((2 * m * i - 1 : ℝ)) ^ m := by
    rw [ht]; push_cast
    refine prod_congr rfl fun i hi => ?_
    have : 1 ≤ 2 * m * i := by
      have := (mem_Icc.1 hi).1; nlinarith
    rw [Nat.cast_sub this]; push_cast; ring
  have hD : H ≤ Real.log s - Real.log t := by rw [hS, hT]; exact harmonic_le_log_sub n m hm
  have htpos : 0 < t := by
    rw [ht]; apply prod_pos; intro i hi
    have := (mem_Icc.1 hi).1; apply pow_pos
    have h3 : 1 ≤ m * i := Nat.mul_pos hm this
    have : 2 * m * i = 2 * (m * i) := by ring
    omega
  have hspos : 0 < s := by
    rw [hs]; apply prod_pos; intro i hi; positivity
  have hT0 : (0 : ℝ) < t := by exact_mod_cast htpos
  have hS0 : (0 : ℝ) < s := by exact_mod_cast hspos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hH1 : (1 : ℝ) ≤ H := by
    rw [hH]; exact_mod_cast (show (1 : ℚ) ≤ harmonic n from by
      rw [harmonic_eq_sum_Icc]
      calc (1:ℚ) = ∑ i ∈ Icc (1:ℕ) 1, ((i:ℚ))⁻¹ := by simp
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hn) (fun _ _ _ => by positivity))
  -- from h2: log s - log t < p/q
  have hlt2 : ((k : ℝ) * q) ^ k * s < ((k : ℝ) * q + p) ^ k * t := by
    have : k^k * q^k * s < (k*q+p)^k * t := by omega
    have : ((k^k * q^k * s : ℕ) : ℝ) < (((k*q+p)^k * t : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; rw [mul_pow]; linarith
  set r : ℝ := (p : ℝ) / q with hr
  have hr0 : 0 < r := by positivity
  have hrD : Real.log s - Real.log t < r := by
    have hkq : (0 : ℝ) < k * q := by positivity
    have e : ((k : ℝ) * q + p) ^ k = ((k : ℝ) * q) ^ k * (1 + r / k) ^ k := by
      rw [← mul_pow]; congr 1; rw [hr]; field_simp
    rw [e] at hlt2
    have h3 : (s : ℝ) < (1 + r / k) ^ k * t := by
      have hpk : (0 : ℝ) < ((k : ℝ) * q) ^ k := by positivity
      nlinarith
    have h4 : (1 + r / k) ^ k ≤ Real.exp r := by
      have : 1 + r / k ≤ Real.exp (r / k) := by linarith [Real.add_one_le_exp (r / k)]
      calc (1 + r / k) ^ k ≤ (Real.exp (r / k)) ^ k := by
            apply pow_le_pow_left₀ (by positivity) this
        _ = Real.exp r := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    have h5 : (s : ℝ) < Real.exp r * t := by nlinarith
    have h6 : Real.log s < Real.log (Real.exp r * t) := Real.log_lt_log hS0 h5
    rw [Real.log_mul (Real.exp_pos r).ne' hT0.ne', Real.log_exp] at h6
    linarith
  -- from h1
  have hlt1 : (k : ℝ) ^ k * (p : ℝ) ^ s * (s : ℝ) ^ t < ((c : ℝ) * t + k) ^ k * (q : ℝ) ^ s * (t : ℝ) ^ t := by
    have : k^k * p^s * s^t < (c*t+k)^k * q^s * t^t := by omega
    exact_mod_cast this
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hL := Real.log_lt_log (by positivity) hlt1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hL
  have hlogk : Real.log ((c : ℝ) * t + k) - Real.log k ≤ c * t / k := by
    rw [← Real.log_div (by positivity) hk0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((c : ℝ) * t + k) / k by positivity)
    have e : ((c : ℝ) * t + k) / k - 1 = c * t / k := by field_simp; ring
    linarith
  have hkey : (s : ℝ) * (Real.log p - Real.log q) + t * (Real.log s - Real.log t) < c * t := by
    have : (k : ℝ) * (Real.log ((c : ℝ) * t + k) - Real.log k) ≤ c * t := by
      calc (k : ℝ) * (Real.log ((c : ℝ) * t + k) - Real.log k) ≤ k * (c * t / k) := by gcongr
        _ = c * t := by field_simp
    nlinarith
  -- conclude
  have hlogr : Real.log p - Real.log q = Real.log r := by rw [hr, Real.log_div hp0.ne' hq0.ne']
  rw [hlogr] at hkey
  set D := Real.log s - Real.log t with hDdef
  have hST : (s : ℝ) = Real.exp D * t := by
    rw [hDdef, Real.exp_sub, Real.exp_log hS0, Real.exp_log hT0]; field_simp
  have hHpos : 0 < H := by linarith
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlr : Real.log H ≤ Real.log r := Real.log_le_log hHpos (by linarith)
  have hexp : Real.exp H ≤ Real.exp D := Real.exp_le_exp.2 hD
  have hmain : Real.exp D * Real.log r + D < c := by
    rw [hST] at hkey
    have e : (t : ℝ) * (Real.exp D * Real.log r + D) = Real.exp D * t * Real.log r + t * D := by ring
    have : (t : ℝ) * (Real.exp D * Real.log r + D) < t * c := by rw [e]; linarith
    exact lt_of_mul_lt_mul_left this hT0.le
  have hfin : H + Real.exp H * Real.log H < c := by
    have : Real.exp H * Real.log H ≤ Real.exp D * Real.log r :=
      mul_le_mul hexp hlr hlogH (Real.exp_pos D).le
    linarith
  have hlag := BroughanRH.lagarias n hn
  rw [← hc] at hlag
  linarith
