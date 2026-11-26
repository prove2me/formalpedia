-- Prove2me | solution 1 for Erdos287.finite_frontier_requires_pair_coefficient_below_3_35
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T16:01:58.66251+00:00
-- url     : https://prove2.me/submissions/ab4f88dc-2d6b-42f1-b448-62fc532dcec8

import Mathlib

set_option autoImplicit false

private theorem mean_le (N B T σ μ n L : ℝ) (hn : 0 < n) (hnN : n ≤ N)
    (hB : 0 ≤ B) (hT : 0 ≤ T ∧ T ≤ 2 * B * N)
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hmean : N * μ ≤ 2 * σ * Real.log (1 + T))
    (hL : Real.log (1 + 2 * B * n) ≤ L) : μ ≤ L / (2 * n) := by
  have hN : 0 < N := hn.trans_le hnN
  have hlog := Real.log_le_log (show 0 < 1 + T by linarith [hT.1])
    (show 1 + T ≤ 1 + 2 * B * N by linarith [hT.2])
  have hscale := mul_le_mul_of_nonneg_right (show 2 * σ ≤ 1 / 2 by linarith [hσ.2])
    (Real.log_nonneg (show 1 ≤ 1 + T by linarith [hT.1]))
  have hbound : 2 * (N * μ) ≤ Real.log (1 + 2 * B * N) := by
    linarith only [hscale, hmean, hlog]
  let w := n / N
  have hw : 0 < w := div_pos hn hN
  have hw1 : w ≤ 1 := (div_le_iff₀ hN).mpr (by simpa using hnN)
  have hwN : w * N = n := div_mul_cancel₀ _ hN.ne'
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show 1 + 2 * B * N ∈ Set.Ioi (0 : ℝ) by change 0 < 1 + 2 * B * N; positivity)
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    hw.le (sub_nonneg.mpr hw1) (show w + (1 - w) = 1 by ring)
  rw [smul_eq_mul, smul_eq_mul, Real.log_one, mul_zero, add_zero,
    smul_eq_mul, smul_eq_mul, mul_one] at hc
  have heq : w * (1 + 2 * B * N) + (1 - w) = 1 + 2 * B * n := by
    linear_combination (2 * B) * hwN
  rw [heq] at hc
  have hs := (mul_le_mul_of_nonneg_left hbound hw.le).trans (hc.trans hL)
  apply (le_div_iff₀ (by positivity : 0 < 2 * n)).mpr
  calc
    μ * (2 * n) = w * (2 * (N * μ)) := by rw [← hwN]; ring
    _ ≤ L := hs

private theorem exp_lower (k : ℕ) (hk : 0 < k) : (2718 / 1000 : ℝ) ^ k < Real.exp k := by
  rw [show (k : ℝ) = k * (1 : ℝ) by ring, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) hk.ne'

/-- At the cofactor budget available at the checked finite frontier, the
one-period grouped sieve test cannot succeed with pair coefficient at least 3.35. -/
theorem solution (B u v : ℕ) (T σ A μ : ℝ) (hB : B ≤ 3187) (hu : 0 < u)
    (hv : (v : ℝ) < Real.exp 1 * (u : ℝ))
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 67 / 20 ≤ A) :
    let N : ℝ := (u : ℝ) + v
    let r := N / (u : ℝ)
    0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N → A < r →
      N * μ ≤ 2 * σ * Real.log (1 + T) → μ * (r - A) ≤ 1 - A * σ := by
  intro N r hT hAr hmean
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  have hB' : (B : ℝ) ≤ 3187 := by exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hAr' : (67 / 20 : ℝ) < r := lt_of_le_of_lt hA hAr
  have hv' : (v : ℝ) < (11 / 4) * (u : ℝ) := hv.trans
    (mul_lt_mul_of_pos_right (by linarith [Real.exp_one_lt_d9]) huR)
  have hr : r < 15 / 4 := by
    apply (div_lt_iff₀ huR).mpr
    dsimp [N]
    linarith
  have hu2 : 2 ≤ u := by
    by_contra! h
    have heq : u = 1 := by omega
    have hv2 : v ≤ 2 := by
      have hsmall' : (v : ℝ) < 11 / 4 := by simpa [heq] using hv'
      have hh : (v : ℝ) < 3 := hsmall'.trans (by norm_num)
      exact Nat.le_of_lt_succ (by exact_mod_cast hh)
    have hN' : N < (67 / 20) * (u : ℝ) := by
      dsimp [N]
      rw [heq]
      norm_num
      have hv2' : (v : ℝ) ≤ 2 := by exact_mod_cast hv2
      linarith
    exact ((lt_div_iff₀ huR).mp hAr').not_gt hN'
  by_contra! hfail
  have hμσ : σ < μ := by
    by_contra! hb
    have hm := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hAr.le)
    have hs := mul_le_mul_of_nonneg_left hσ.2 (show 0 ≤ r by linarith)
    linarith only [hm, hs, hr, hfail]
  have hswap := mul_le_mul_of_nonneg_right hA (sub_nonneg.mpr hμσ.le)
  have hsig := mul_le_mul_of_nonneg_left hσ.2 (show (0 : ℝ) ≤ 67 / 20 by norm_num)
  have hneed : (13 / 80 : ℝ) < μ * (r - 67 / 20) := by
    linarith only [hswap, hsig, hfail]
  have hNlower : (67 / 20 : ℝ) * (u : ℝ) < N := (lt_div_iff₀ huR).mp hAr'
  by_cases hsmall : r ≤ 7 / 2
  · have hu2' : (2 : ℝ) ≤ u := by exact_mod_cast hu2
    have hN7 : 7 ≤ u + v := by
      by_contra! h
      have h6 : u + v ≤ 6 := by omega
      have h6' : (u : ℝ) + v ≤ 6 := by exact_mod_cast h6
      change (67 / 20 : ℝ) * (u : ℝ) < (u : ℝ) + v at hNlower
      linarith
    have hN7' : (7 : ℝ) ≤ N := by
      change 7 ≤ (u : ℝ) + v
      exact_mod_cast hN7
    have hlog : Real.log (1 + 2 * (B : ℝ) * 7) ≤ 11 := by
      apply (Real.log_le_iff_le_exp (by positivity)).mpr
      calc
        1 + 2 * (B : ℝ) * 7 ≤ (2718 / 1000 : ℝ) ^ 11 := by norm_num; linarith
        _ ≤ Real.exp 11 := (exp_lower 11 (by decide)).le
    have hμ := mean_le N B T σ μ 7 11 (by norm_num) hN7' hB0 hT hσ hmean hlog
    have hb := mul_le_mul_of_nonneg_right hμ (sub_nonneg.mpr hAr'.le)
    linarith only [hb, hsmall, hneed]
  · by_cases hmid : r ≤ 11 / 3
    · have hN11 : 11 ≤ u + v := by
        by_contra! h
        have h10 : u + v ≤ 10 := by omega
        have h10' : (u : ℝ) + v ≤ 10 := by exact_mod_cast h10
        have hlarge : (7 / 2 : ℝ) * (u : ℝ) < N := (lt_div_iff₀ huR).mp (lt_of_not_ge hsmall)
        have hu3 : u < 3 := by
          by_contra! h
          have hh : (3 : ℝ) ≤ u := by exact_mod_cast h
          change (7 / 2 : ℝ) * (u : ℝ) < (u : ℝ) + v at hlarge
          linarith
        have heq : u = 2 := by omega
        have hvlo : (5 : ℝ) < v := by
          change (7 / 2 : ℝ) * (u : ℝ) < (u : ℝ) + v at hlarge
          norm_num [heq] at hlarge
          linarith
        have hvhi : (v : ℝ) < 6 := by norm_num [heq] at hv'; linarith
        have h1 : 5 < v := by exact_mod_cast hvlo
        have h2 : v < 6 := by exact_mod_cast hvhi
        omega
      have hN11' : (11 : ℝ) ≤ N := by
        change 11 ≤ (u : ℝ) + v
        exact_mod_cast hN11
      have hlog : Real.log (1 + 2 * (B : ℝ) * 11) ≤ 56 / 5 := by
        apply (Real.log_le_iff_le_exp (by positivity)).mpr
        rw [show (56 / 5 : ℝ) = 11 + 1 / 5 by norm_num, Real.exp_add]
        calc
          1 + 2 * (B : ℝ) * 11 ≤ (2718 / 1000 : ℝ) ^ 11 * (1 + 1 / 5) := by
            norm_num
            linarith
          _ ≤ Real.exp 11 * Real.exp (1 / 5) :=
            mul_le_mul (exp_lower 11 (by decide)).le (by linarith [Real.add_one_le_exp (1 / 5)])
              (by norm_num) (Real.exp_nonneg _)
      have hμ := mean_le N B T σ μ 11 (56 / 5) (by norm_num) hN11' hB0 hT hσ hmean hlog
      have hb := mul_le_mul_of_nonneg_right hμ (sub_nonneg.mpr hAr'.le)
      linarith only [hb, hmid, hneed]
    · have hlarge : (11 / 3 : ℝ) * (u : ℝ) < N := (lt_div_iff₀ huR).mp (lt_of_not_ge hmid)
      have h1 : 8 * u < 3 * v := by
        have hh : 8 * (u : ℝ) < 3 * (v : ℝ) := by
          change (11 / 3 : ℝ) * (u : ℝ) < (u : ℝ) + v at hlarge
          linarith
        exact_mod_cast hh
      have h2 : 4 * v < 11 * u := by
        have hh : 4 * (v : ℝ) < 11 * (u : ℝ) := by linarith
        exact_mod_cast hh
      have hN26 : 26 ≤ u + v := by omega
      have hN26' : (26 : ℝ) ≤ N := by
        change 26 ≤ (u : ℝ) + v
        exact_mod_cast hN26
      have hlog : Real.log (1 + 2 * (B : ℝ) * 26) ≤ 13 := by
        apply (Real.log_le_iff_le_exp (by positivity)).mpr
        calc
          1 + 2 * (B : ℝ) * 26 ≤ (2718 / 1000 : ℝ) ^ 13 := by norm_num; linarith
          _ ≤ Real.exp 13 := (exp_lower 13 (by decide)).le
      have hμ := mean_le N B T σ μ 26 13 (by norm_num) hN26' hB0 hT hσ hmean hlog
      have hb := mul_le_mul_of_nonneg_right hμ (sub_nonneg.mpr hAr'.le)
      linarith only [hb, hr, hneed]

