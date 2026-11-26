-- Prove2me | solution 1 for Erdos287.chen_grouped_moment_doubly_exponential_scale
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T17:23:31.258934+00:00
-- url     : https://prove2.me/submissions/4b308ac5-cb37-434c-855f-2083030b3d37

import Mathlib

set_option autoImplicit false

private theorem bound_from_successor_power (B b M : ℕ) (hb : b < B)
    (h : (2 : ℕ) ^ B < 2 * M) : (2 : ℕ) ^ b < M := by
  have hpow : (2 : ℕ) ^ (b + 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by decide) hb
  have hstrict := hpow.trans_lt h
  rw [pow_succ] at hstrict
  omega

private theorem log_budget_constant : 1 + 290 * (2 : ℝ) ^ (7800 : ℕ) ≤ Real.exp 5510 := by
  have hexp7 : (2 : ℝ) ^ (10 : ℕ) < Real.exp 7 := by
    rw [show (7 : ℝ) = (7 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    calc
      (2 : ℝ) ^ (10 : ℕ) < (27 / 10 : ℝ) ^ (7 : ℕ) := by norm_num
      _ < _ := pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by decide)
  have hpow1 : (1 : ℝ) ≤ 2 ^ (7800 : ℕ) := one_le_pow₀ (by norm_num)
  calc
    1 + 290 * (2 : ℝ) ^ (7800 : ℕ) ≤ 291 * (2 : ℝ) ^ (7800 : ℕ) := by
      rw [show (291 : ℝ) = 1 + 290 by norm_num, add_mul, one_mul]
      exact add_le_add hpow1 le_rfl
    _ ≤ 2 ^ (10 : ℕ) * 2 ^ (7800 : ℕ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = ((2 : ℝ) ^ (10 : ℕ)) ^ (781 : ℕ) := by rw [← pow_add, ← pow_mul]
    _ ≤ (Real.exp 7) ^ (781 : ℕ) := pow_le_pow_left₀ (by positivity) hexp7.le _
    _ = Real.exp (7 * 781) := by
      rw [mul_comm (7 : ℝ)]
      simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (7 : ℝ) 781).symm
    _ ≤ Real.exp 5510 := Real.exp_le_exp.mpr (by norm_num)

/-- With the elementary lcm omission rule, a grouped moment test of this
strength requires a doubly exponential denominator scale. -/
theorem solution (B p M u v : ℕ) (T σ A μ : ℝ) (hu : 0 < u)
    (hv : (v : ℝ) < Real.exp 1 * (u : ℝ))
    (hB : B * Nat.lcmUpto B < p) (hp : p ≤ M)
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 743 / 200 ≤ A) :
    let N : ℝ := (u : ℝ) + v
    let r := N / (u : ℝ)
    0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N → A < r →
      N * μ ≤ 2 * σ * Real.log (1 + T) →
      1 - A * σ < μ * (r - A) → (2 : ℕ) ^ (2 ^ (7800 : ℕ)) < M := by
  intro N r hT hAr hmean htest
  have hu' : 0 < (u : ℝ) := by exact_mod_cast hu
  have hvhi : 32 * v < 87 * u := by
    have hb : Real.exp 1 < (87 / 32 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hc := hv.trans (mul_lt_mul_of_pos_right hb hu')
    have hd : 32 * (v : ℝ) < 87 * (u : ℝ) := by linarith
    exact_mod_cast hd
  have hvlo : 19 * u < 7 * v := by
    have hh := (lt_div_iff₀ hu').mp (hA.trans_lt hAr)
    change (743 / 200 : ℝ) * u < (u : ℝ) + v at hh
    have hl := mul_lt_mul_of_pos_right (by norm_num : (26 / 7 : ℝ) < 743 / 200) hu'
    have hd : 19 * (u : ℝ) < 7 * (v : ℝ) := by linarith
    exact_mod_cast hd
  have hcount : 145 ≤ u + v := by omega
  have hN : 145 ≤ N := by
    change 145 ≤ (u : ℝ) + v
    exact_mod_cast hcount
  have hNp : 0 < N := by linarith
  have hr : r < 119 / 32 := by
    apply (div_lt_iff₀ hu').mpr
    have h : 32 * (v : ℝ) < 87 * (u : ℝ) := by exact_mod_cast hvhi
    dsimp [N]
    linarith
  have hμ : 19 < μ := by
    by_contra! h
    have htest' := mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hAr.le)
    have hprod := mul_le_mul_of_nonneg_left hσ.2 (show 0 ≤ A by linarith)
    linarith only [htest', hprod, hA, hr, htest]
  have hlog : Real.log (1 + T) ≤ Real.log (1 + 2 * (B : ℝ) * N) :=
    Real.log_le_log (by linarith [hT.1]) (by linarith [hT.2])
  have hlog0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith [hT.1])
  have hscaled := mul_le_mul_of_nonneg_right (show 2 * σ ≤ 1 / 2 by linarith [hσ.2]) hlog0
  have hstrict := mul_lt_mul_of_pos_left hμ hNp
  have hbig : 38 * N < Real.log (1 + 2 * (B : ℝ) * N) := by
    linarith only [hscaled, hmean, hstrict, hlog]
  let w : ℝ := 145 / N
  have hw : 0 < w := div_pos (by norm_num) hNp
  have hw1 : w ≤ 1 := (div_le_iff₀ hNp).mpr (by simpa using hN)
  have hwN : w * N = 145 := div_mul_cancel₀ _ hNp.ne'
  have hcon := strictConcaveOn_log_Ioi.concaveOn.2
    (show 1 + 2 * (B : ℝ) * N ∈ Set.Ioi (0 : ℝ) by change 0 < 1 + 2 * (B : ℝ) * N; positivity)
    (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num)
    hw.le (sub_nonneg.mpr hw1) (show w + (1 - w) = 1 by ring)
  rw [smul_eq_mul, smul_eq_mul, Real.log_one, mul_zero, add_zero,
    smul_eq_mul, smul_eq_mul, mul_one] at hcon
  have harg : w * (1 + 2 * (B : ℝ) * N) + (1 - w) = 1 + 290 * (B : ℝ) := by
    linear_combination (2 * (B : ℝ)) * hwN
  rw [harg] at hcon
  have hneed : 5510 < Real.log (1 + 290 * (B : ℝ)) := by
    calc
      (5510 : ℝ) = w * (38 * N) := by rw [← mul_left_comm, hwN]; norm_num
      _ < _ := (mul_lt_mul_of_pos_left hbig hw).trans_le hcon
  have hBlarge : (2 : ℕ) ^ (7800 : ℕ) < B := by
    apply not_le.mp
    intro h
    have h' : (B : ℝ) ≤ (2 : ℝ) ^ (7800 : ℕ) := by exact_mod_cast h
    have hbound : 1 + 290 * (B : ℝ) ≤ Real.exp 5510 := by
      exact (add_le_add (le_refl (1 : ℝ))
        (mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℝ) ≤ 290))).trans
        log_budget_constant
    have hpos : 0 < 1 + 290 * (B : ℝ) :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (by norm_num) (Nat.cast_nonneg B))
    have hlogged : Real.log (1 + 290 * (B : ℝ)) ≤ 5510 := (Real.log_le_iff_le_exp hpos).mpr hbound
    exact hneed.not_ge hlogged
  have hBpos : 0 < B := Nat.zero_lt_of_lt hBlarge
  have hbound : (2 : ℕ) ^ B < 2 * M := calc
    2 ^ B ≤ (B + 1) * Nat.lcmUpto B := Chebyshev.two_pow_le_mul_lcmUpto B
    _ ≤ 2 * (B * Nat.lcmUpto B) := by
      simpa only [mul_assoc] using Nat.mul_le_mul_right (Nat.lcmUpto B) (show B + 1 ≤ 2 * B by omega)
    _ < 2 * p := Nat.mul_lt_mul_of_pos_left hB (by decide)
    _ ≤ 2 * M := Nat.mul_le_mul_left _ hp
  exact bound_from_successor_power B (2 ^ (7800 : ℕ)) M hBlarge hbound

