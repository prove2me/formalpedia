-- Prove2me | solution 1 for EulerMascheroni.Rivoal.den_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:20:33.131908+00:00
-- url     : https://prove2.me/submissions/f65da1a3-3a54-4fa1-b4da-712d811025fd

import Definitions.Def_eulerMascheroni_rivoalForms
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

namespace RivoalEasy
open EulerMascheroni.Rivoal

theorem den_dvd (n : ℕ) : den n ∣ Nat.lcmUpto (3 * n) := by
  refine Finset.lcm_dvd fun i hi => ?_
  simp only [Finset.mem_range] at hi
  show i + 1 ∣ _
  have hmem : i + 1 ∈ Finset.Icc 1 (3 * n) := by simp only [Finset.mem_Icc]; omega
  exact Finset.dvd_lcm (f := id) hmem

theorem pow_log_le (p m : ℕ) (hp : 2 ≤ p) (hm : m ≠ 0) :
    p ^ Nat.log p m ≤ p * (if p * p ≤ m then m else 1) := by
  split_ifs with h
  · exact le_trans (Nat.pow_log_le_self p hm) (Nat.le_mul_of_pos_left m (by omega))
  · have : Nat.log p m < 2 := Nat.log_lt_of_lt_pow hm (by rw [sq]; omega)
    calc p ^ Nat.log p m ≤ p ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = p * 1 := by ring

theorem lcmUpto_le (m : ℕ) : Nat.lcmUpto m ≤ 4 ^ m * m ^ Nat.sqrt m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Nat.lcmUpto]
  rw [Nat.lcmUpto_eq_prod_pow_log]
  have hcard : ((Nat.primesLE m).filter (fun p => p * p ≤ m)).card ≤ Nat.sqrt m := by
    calc _ ≤ (Finset.Icc 1 (Nat.sqrt m)).card := by
          refine Finset.card_le_card fun p hp => ?_
          simp only [Finset.mem_filter] at hp
          have := (Nat.prime_of_mem_primesLE hp.1).two_le
          simp only [Finset.mem_Icc]
          exact ⟨by omega, Nat.le_sqrt.mpr hp.2⟩
      _ = Nat.sqrt m := by simp
  calc ∏ p ∈ Nat.primesLE m, p ^ Nat.log p m
      ≤ ∏ p ∈ Nat.primesLE m, p * (if p * p ≤ m then m else 1) :=
        Finset.prod_le_prod' fun p hp =>
          pow_log_le p m (Nat.prime_of_mem_primesLE hp).two_le (by omega)
    _ = primorial m * m ^ ((Nat.primesLE m).filter (fun p => p * p ≤ m)).card := by
        rw [Finset.prod_mul_distrib, ← Finset.prod_filter, Finset.prod_const]
        rfl
    _ ≤ 4 ^ m * m ^ Nat.sqrt m :=
        Nat.mul_le_mul (primorial_le_four_pow m) (Nat.pow_le_pow_right hm hcard)

theorem log_le_div_e {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.add_one_le_exp (Real.log y - 1)
  rw [Real.exp_sub, Real.exp_log hy] at h
  linarith

theorem two_div_e_le : 2 / Real.exp 1 ≤ Real.log (11 / 4) := by
  have he := Real.exp_one_gt_d9
  have he' := Real.exp_one_lt_d9
  have h1 : 2 / Real.exp 1 ≤ 3 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  refine le_trans h1 ?_
  rw [Real.le_log_iff_exp_le (by norm_num)]
  by_contra hc
  push Not at hc
  have h4 : (11 / 4 : ℝ) ^ 4 < Real.exp (3 / 4) ^ 4 :=
    pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
  have e : Real.exp (3 / 4) ^ 4 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  rw [e] at h4
  have h5 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := pow_lt_pow_left₀ he' (by linarith) (by norm_num)
  norm_num at h4 h5
  linarith

theorem pow_sqrt_le (m : ℕ) : ((m : ℝ) ^ Nat.sqrt m) ≤ (11 / 4 : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < m := by linarith
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg hm'
  have hs : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := Real.nat_sqrt_le_real_sqrt
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hpos
  have hl : Real.log m ≤ 2 * (Real.sqrt m / Real.exp 1) := by
    have := log_le_div_e hsq
    rw [Real.log_sqrt hpos.le] at this
    linarith
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hpos.le
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  calc (Nat.sqrt m : ℝ) * Real.log m ≤ Real.sqrt m * (2 * (Real.sqrt m / Real.exp 1)) :=
        mul_le_mul hs hl hlog0 hsq.le
    _ = (2 / Real.exp 1) * (Real.sqrt m * Real.sqrt m) := by ring
    _ = (2 / Real.exp 1) * m := by rw [hmm]
    _ ≤ Real.log (11 / 4) * m := mul_le_mul_of_nonneg_right two_div_e_le hpos.le
    _ = _ := by ring

end RivoalEasy

theorem solution (n : ℕ) :
    (EulerMascheroni.Rivoal.den n : ℝ) ≤ 11 ^ (3 * n) := by
  have h1 : EulerMascheroni.Rivoal.den n ≤ 4 ^ (3 * n) * (3 * n) ^ Nat.sqrt (3 * n) :=
    le_trans (Nat.le_of_dvd (Nat.lcmUpto_pos _) (RivoalEasy.den_dvd n))
      (RivoalEasy.lcmUpto_le _)
  have h2 : (EulerMascheroni.Rivoal.den n : ℝ) ≤ 4 ^ (3 * n) * ((3 * n : ℕ) : ℝ) ^ Nat.sqrt (3 * n) := by
    exact_mod_cast h1
  refine le_trans h2 ?_
  calc (4 : ℝ) ^ (3 * n) * ((3 * n : ℕ) : ℝ) ^ Nat.sqrt (3 * n)
      ≤ 4 ^ (3 * n) * (11 / 4) ^ (3 * n) := by
        gcongr; exact RivoalEasy.pow_sqrt_le _
    _ = 11 ^ (3 * n) := by rw [← mul_pow]; norm_num
