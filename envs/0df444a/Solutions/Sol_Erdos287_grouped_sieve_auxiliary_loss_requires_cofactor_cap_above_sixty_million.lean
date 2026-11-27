-- Prove2me | solution 1 for Erdos287.grouped_sieve_auxiliary_loss_requires_cofactor_cap_above_sixty_million
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:13:33.978449+00:00
-- url     : https://prove2.me/submissions/b6856872-b1d4-4e08-a866-98396aa9dc5c

import Mathlib

set_option autoImplicit false

private theorem scaledMeanBound (B N n T s μ L : ℝ) (hB : 0 ≤ B)
    (hn : 0 < n) (hnN : n ≤ N) (hT : 0 ≤ T ∧ T ≤ 2 * B * N)
    (hs : 0 ≤ s) (hmean : N * μ ≤ s * Real.log (1 + T))
    (hL : Real.log (1 + 2 * B * n) ≤ L) : μ ≤ s * (L / n) := by
  have hN : 0 < N := hn.trans_le hnN
  have hlog := Real.log_le_log (show 0 < 1 + T by linarith [hT.1])
    (show 1 + T ≤ 1 + 2 * B * N by linarith [hT.2])
  have hbound := hmean.trans (mul_le_mul_of_nonneg_left hlog hs)
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
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hn).mpr
  calc
    μ * n = w * (N * μ) := by rw [← hwN]; ring
    _ ≤ w * (s * Real.log (1 + 2 * B * N)) := mul_le_mul_of_nonneg_left hbound hw.le
    _ = s * (w * Real.log (1 + 2 * B * N)) := by ring
    _ ≤ s * L := mul_le_mul_of_nonneg_left (hc.trans hL) hs

private theorem expLower (k : ℕ) (hk : 0 < k) : (2718 / 1000 : ℝ) ^ k < Real.exp k := by
  rw [show (k : ℝ) = k * (1 : ℝ) by ring, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) hk.ne'

private theorem quadraticBound (R L s : ℝ) (hRL : 0 < R * L)
    (hdisc : ((R - 2) * L + 2) ^ 2 < 4 * (R * L)) :
    s * L * (R * (1 - s) - 2) + 2 * s < 1 := by
  have hsq := sq_nonneg (2 * (R * L) * s - ((R - 2) * L + 2))
  have heq : 4 * (R * L) * (s * L * (R * (1 - s) - 2) + 2 * s - 1) =
      ((R - 2) * L + 2) ^ 2 - 4 * (R * L) -
        (2 * (R * L) * s - ((R - 2) * L + 2)) ^ 2 := by ring
  by_contra! hfail
  have hprod := mul_nonneg (show 0 ≤ 4 * (R * L) by positivity) (sub_nonneg.mpr hfail)
  linarith only [heq, hprod, hdisc, hsq]

/-- At cofactor cap sixty million, the grouped first and second moments
cannot pass when the pair coefficient pays twice the support radius out
of a total distribution level of at most one. -/
theorem solution (B u v : ℕ) (T σ A μ : ℝ) (hB : B ≤ 60000000) (hu : 0 < u)
    (hv : (v : ℝ) < Real.exp 1 * (u : ℝ)) (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) :
    let N : ℝ := (u : ℝ) + v
    let r := N / (u : ℝ)
    0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N →
    2 / (1 - 2 * σ) ≤ A → A < r →
    N * μ ≤ 2 * σ * Real.log (1 + T) →
    μ * (r - A) ≤ 1 - A * σ := by
  intro N r hT hA hAr hmean
  let s := 2 * σ
  let A₀ := (2 : ℝ) / (1 - s)
  have hs : 0 ≤ s := by dsimp [s]; linarith [hσ.1]
  have hs₁ : 0 < 1 - s := by dsimp [s]; linarith [hσ.2]
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  have huv : (v : ℝ) < (68 / 25) * (u : ℝ) := hv.trans
    (mul_lt_mul_of_pos_right (by linarith [Real.exp_one_lt_d9]) huR)
  have hr : r < 93 / 25 := by
    apply (div_lt_iff₀ huR).mpr
    dsimp [N]
    linarith
  have hA₀ : A₀ * (1 - s) = 2 := div_mul_cancel₀ _ hs₁.ne'
  have hA₂ : (2 : ℝ) ≤ A₀ := by
    apply (le_div_iff₀ hs₁).mpr
    linarith
  have hr₂ : (2 : ℝ) < r := hA₂.trans_lt (hA.trans_lt hAr)
  have hPos : 0 < r * (1 - s) - 2 := by
    have h := mul_lt_mul_of_pos_right (hA.trans_lt hAr : A₀ < r) hs₁
    linarith
  have hb : (B : ℝ) ≤ 60000000 := by exact_mod_cast hB
  by_contra! htest
  have hμσ : σ < μ := by
    by_contra! h
    have htest' := mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hAr.le)
    have hrσ := mul_le_mul_of_nonneg_left hσ.2 (show 0 ≤ r by linarith only [hr₂])
    linarith only [htest', hrσ, hr, htest]
  have hswap := mul_le_mul_of_nonneg_right (show A₀ ≤ A from hA) (sub_nonneg.mpr hμσ.le)
  have htest₀ : 1 < μ * (r - A₀) + A₀ * σ := by linarith only [hswap, htest]
  have hneed : 1 < μ * (r * (1 - s) - 2) + 2 * s := by
    have h := mul_lt_mul_of_pos_right htest₀ hs₁
    have heq : (μ * (r - A₀) + A₀ * σ) * (1 - s) = μ * (r * (1 - s) - 2) + s := by
      change (μ * (r - A₀) + A₀ * σ) * (1 - s) = μ * (r * (1 - s) - 2) + 2 * σ
      linear_combination (σ - μ) * hA₀
    rw [heq, one_mul] at h
    linarith only [h]
  have reject (n L R : ℝ) (hn : 0 < n) (hnN : n ≤ N) (hL : 0 ≤ L) (hrR : r ≤ R)
      (hlog : Real.log (1 + 2 * (B : ℝ) * n) ≤ L)
      (hquad : s * (L / n) * (R * (1 - s) - 2) + 2 * s < 1) : False := by
    have hcap := scaledMeanBound B N n T s μ L (Nat.cast_nonneg B) hn hnN hT hs hmean hlog
    have hpart := mul_le_mul_of_nonneg_right hcap hPos.le
    have hm := mul_le_mul_of_nonneg_right hrR hs₁.le
    have hpart' := mul_le_mul_of_nonneg_left (sub_le_sub_right hm 2)
      (mul_nonneg hs (div_nonneg hL hn.le))
    linarith only [hneed, hpart, hpart', hquad]
  have huOne : (1 : ℝ) ≤ u := by exact_mod_cast hu
  by_cases hsmall : r ≤ 3
  · have hN₃ : (3 : ℝ) ≤ N := by
      have hrN := (lt_div_iff₀ huR).mp hr₂
      have htwo := mul_le_mul_of_nonneg_left huOne (show (0 : ℝ) ≤ 2 by norm_num)
      change (2 : ℝ) * u < (u : ℝ) + v at hrN
      have hInt : 2 < u + v := by exact_mod_cast (show (2 : ℝ) < (u : ℝ) + v by linarith)
      change (3 : ℝ) ≤ (u : ℝ) + v
      exact_mod_cast (show 3 ≤ u + v by omega)
    refine reject 3 20 3 (by norm_num) hN₃ (by norm_num) hsmall ?_ ?_
    · apply (Real.log_le_iff_le_exp (by positivity)).mpr
      exact (show 1 + 2 * (B : ℝ) * 3 ≤ (2718 / 1000 : ℝ) ^ (20 : ℕ) by norm_num; linarith).trans
        (expLower 20 (by decide)).le
    · exact quadraticBound 3 (20 / 3) s (by norm_num) (by norm_num)
  · have huTwo : 2 ≤ u := by
      by_contra! h
      have heq : u = 1 := by omega
      have hval := (lt_div_iff₀ huR).mp (lt_of_not_ge hsmall)
      change (3 : ℝ) * (u : ℝ) < (u : ℝ) + v at hval
      norm_num [heq] at hval huv
      have hva : 2 < v := by exact_mod_cast (show (2 : ℝ) < v by linarith)
      have hvb : v < 3 := by exact_mod_cast (show (v : ℝ) < 3 by linarith)
      omega
    by_cases hmid : r ≤ 7 / 2
    · have hN₇ : (7 : ℝ) ≤ N := by
        have hval := (lt_div_iff₀ huR).mp (lt_of_not_ge hsmall)
        have huTwo' : (2 : ℝ) ≤ u := by exact_mod_cast huTwo
        change (3 : ℝ) * u < (u : ℝ) + v at hval
        have hi : 6 < u + v := by exact_mod_cast (show (6 : ℝ) < (u : ℝ) + v by linarith)
        change (7 : ℝ) ≤ (u : ℝ) + v
        exact_mod_cast (show 7 ≤ u + v by omega)
      refine reject 7 (103 / 5) (7 / 2) (by norm_num) hN₇ (by norm_num) hmid ?_ ?_
      · apply (Real.log_le_iff_le_exp (by positivity)).mpr
        rw [show (103 / 5 : ℝ) = 20 + 3 / 5 by norm_num, Real.exp_add]
        have htaylor := Real.sum_le_exp_of_nonneg (show 0 ≤ (3 / 5 : ℝ) by norm_num) 3
        norm_num [Finset.sum_range_succ] at htaylor
        calc
          1 + 2 * (B : ℝ) * 7 ≤ (2718 / 1000 : ℝ) ^ (20 : ℕ) * (89 / 50) := by
            norm_num
            linarith
          _ ≤ Real.exp 20 * Real.exp (3 / 5) :=
            mul_le_mul (expLower 20 (by decide)).le (by linarith) (by norm_num) (Real.exp_nonneg _)
      · exact quadraticBound (7 / 2) ((103 / 5) / 7) s (by norm_num) (by norm_num)
    · have hN₁₁ : (11 : ℝ) ≤ N := by
        have hval := (lt_div_iff₀ huR).mp (lt_of_not_ge hmid)
        have huThree : 3 ≤ u := by
          by_contra! h
          have heq : u = 2 := by omega
          change (7 / 2 : ℝ) * (u : ℝ) < (u : ℝ) + v at hval
          norm_num [heq] at hval huv
          have hva : 5 < v := by exact_mod_cast (show (5 : ℝ) < v by linarith)
          have hvb : v < 6 := by exact_mod_cast (show (v : ℝ) < 6 by linarith)
          omega
        have huThree' : (3 : ℝ) ≤ u := by exact_mod_cast huThree
        change (7 / 2 : ℝ) * u < (u : ℝ) + v at hval
        have hi : 10 < u + v := by exact_mod_cast (show (10 : ℝ) < (u : ℝ) + v by linarith)
        change (11 : ℝ) ≤ (u : ℝ) + v
        exact_mod_cast (show 11 ≤ u + v by omega)
      refine reject 11 (211 / 10) (93 / 25) (by norm_num) hN₁₁ (by norm_num) hr.le ?_ ?_
      · apply (Real.log_le_iff_le_exp (by positivity)).mpr
        rw [show (211 / 10 : ℝ) = 21 + 1 / 10 by norm_num, Real.exp_add]
        calc
          1 + 2 * (B : ℝ) * 11 ≤ (2718 / 1000 : ℝ) ^ (21 : ℕ) * (11 / 10) := by
            norm_num
            linarith
          _ ≤ Real.exp 21 * Real.exp (1 / 10) :=
            mul_le_mul (expLower 21 (by decide)).le
              (by linarith [Real.add_one_le_exp (1 / 10)]) (by norm_num) (Real.exp_nonneg _)
      · exact quadraticBound (93 / 25) ((211 / 10) / 11) s (by norm_num) (by norm_num)

