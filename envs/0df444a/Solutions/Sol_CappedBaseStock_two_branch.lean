-- Prove2me | solution 1 for CappedBaseStock.two_branch
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:30:06.3968+00:00
-- url     : https://prove2.me/submissions/fdf37b0b-d2fe-4ebb-9256-1e76d89b884d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

-- Compare the bounds through their quadratic square certificate.
private lemma two_branch_real (rho lam Ch Cp : ℝ)
    (hrho_lower : 1 / 2 ≤ rho) (hrho_upper : rho ≤ 1)
    (hlam : 0 < lam) (hCh : 0 ≤ Ch) (hCp : 0 ≤ Cp) :
    min ((1 + 1 / lam) * Ch + (1 + rho) * Cp)
      (2 * Ch + (1 + rho + lam * rho) * Cp) ≤
      (1 + 4 * rho ^ 2 / (4 * rho - 1)) * (Ch + Cp) := by
  let k : ℝ := 1 + 4 * rho ^ 2 / (4 * rho - 1)
  change min ((1 + 1 / lam) * Ch + (1 + rho) * Cp)
    (2 * Ch + (1 + rho + lam * rho) * Cp) ≤ k * (Ch + Cp)
  have hrho : 0 ≤ rho := by linarith
  have hd : 0 < 4 * rho - 1 := by linarith
  have hk_eq : (k - 1) * (4 * rho - 1) = 4 * rho ^ 2 := by
    dsimp [k]
    field_simp [ne_of_gt hd]
    ring
  have hk : 2 ≤ k := by
    by_contra h
    have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge h)) hd
    nlinarith only [hk_eq, hneg, sq_nonneg (2 * rho - 1)]
  have hbase : 1 + rho ≤ k := by linarith
  have hquad : rho ≤ (k - 1) * (1 - lam + lam ^ 2 * rho) := by
    have hcert :
        ((k - 1) * (1 - lam + lam ^ 2 * rho) - rho) * (4 * rho - 1) =
          rho * (2 * lam * rho - 1) ^ 2 := by
      calc
        _ = ((k - 1) * (4 * rho - 1)) * (1 - lam + lam ^ 2 * rho) -
            rho * (4 * rho - 1) := by ring
        _ = _ := by rw [hk_eq]; ring
    have hnonneg := mul_nonneg hrho (sq_nonneg (2 * lam * rho - 1))
    by_contra h
    have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge h)) hd
    nlinarith only [hcert, hnonneg, hneg]
  by_cases hcoef : 1 + 1 / lam ≤ k
  · apply (min_le_left _ _).trans
    calc
      _ ≤ k * Ch + k * Cp :=
        add_le_add (mul_le_mul_of_nonneg_right hcoef hCh)
          (mul_le_mul_of_nonneg_right hbase hCp)
      _ = _ := by ring
  · by_contra hnot
    have hmin := lt_of_not_ge hnot
    have hfirst := lt_of_lt_of_le hmin (min_le_left _ _)
    have hsecond := lt_of_lt_of_le hmin (min_le_right _ _)
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam
    have hinv : lam * (1 + 1 / lam) = lam + 1 := by
      field_simp [hlam_ne]
    have hweight : 0 < 1 + lam - lam * k := by
      have h := mul_lt_mul_of_pos_left (lt_of_not_ge hcoef) hlam
      rw [hinv] at h
      linarith
    have hfirst_scaled : lam * (k * (Ch + Cp)) <
        (lam + 1) * Ch + lam * (1 + rho) * Cp := by
      calc
        _ < lam * ((1 + 1 / lam) * Ch + (1 + rho) * Cp) :=
          mul_lt_mul_of_pos_left hfirst hlam
        _ = _ := by rw [mul_add, ← mul_assoc, hinv]; ring
    have hweighted_first := mul_le_mul_of_nonneg_left hfirst_scaled.le
      (show 0 ≤ k - 2 by linarith)
    have hweighted_second := mul_lt_mul_of_pos_left hsecond hweight
    have hremaining := mul_nonneg (sub_nonneg.mpr hquad) hCp
    nlinarith only [hweighted_first, hweighted_second, hremaining]


-- Specialize the real-parameter inequality to the lead time in Proposition 4.
theorem solution
    (L : ℕ) (hL : 1 ≤ L)
    (lambda C_h C_p : ℝ)
    (hlambda : 0 < lambda) (hC_h : 0 ≤ C_h) (hC_p : 0 ≤ C_p) :
    min
      ((1 + 1 / lambda) * C_h + (1 + (L : ℝ) / ((L : ℝ) + 1)) * C_p)
      (2 * C_h +
        (1 + (L : ℝ) / ((L : ℝ) + 1) +
          lambda * ((L : ℝ) / ((L : ℝ) + 1))) * C_p) ≤
      (1 + 4 * (L : ℝ) ^ 2 / (((L : ℝ) + 1) * (3 * (L : ℝ) - 1))) *
        (C_h + C_p)  := by
  have hLreal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hden : 0 < (L : ℝ) + 1 := by linarith
  have hthree : 0 < 3 * (L : ℝ) - 1 := by linarith
  have hrho_lower : (1 : ℝ) / 2 ≤ (L : ℝ) / ((L : ℝ) + 1) := by
    apply (le_div_iff₀ hden).2
    linarith
  have hrho_upper : (L : ℝ) / ((L : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hd : 0 < 4 * ((L : ℝ) / ((L : ℝ) + 1)) - 1 := by linarith
  have hk :
      1 + 4 * ((L : ℝ) / ((L : ℝ) + 1)) ^ 2 /
          (4 * ((L : ℝ) / ((L : ℝ) + 1)) - 1) =
        1 + 4 * (L : ℝ) ^ 2 / (((L : ℝ) + 1) * (3 * (L : ℝ) - 1)) := by
    field_simp
    ring
  simpa only [hk] using
    two_branch_real ((L : ℝ) / ((L : ℝ) + 1)) lambda C_h C_p
      hrho_lower hrho_upper hlambda hC_h hC_p
