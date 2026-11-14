-- Prove2me | solution 1 for ConsistentSubmodular.threshold_attainer_eligible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:32.214195+00:00
-- url     : https://prove2.me/submissions/59ffb50f-9a75-42fd-aae6-f495d765430b

import Mathlib

section

namespace ConsistentSubmodular

theorem cubic_bernstein_lower (t c₀ c₁ c₂ c₃ l : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h₀ : l ≤ c₀) (h₁ : l ≤ c₁) (h₂ : l ≤ c₂) (h₃ : l ≤ c₃) :
    l ≤ c₀ * (1 - t) ^ 3 + 3 * c₁ * t * (1 - t) ^ 2 +
      3 * c₂ * t ^ 2 * (1 - t) + c₃ * t ^ 3 := by
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hn : 0 ≤ (c₀ - l) * (1 - t) ^ 3 + 3 * (c₁ - l) * t * (1 - t) ^ 2 +
      3 * (c₂ - l) * t ^ 2 * (1 - t) + (c₃ - l) * t ^ 3 := by
    have := sub_nonneg.mpr h₀
    have := sub_nonneg.mpr h₁
    have := sub_nonneg.mpr h₂
    have := sub_nonneg.mpr h₃
    positivity
  nlinarith only [hn]

theorem eligibility_threshold_cubic (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 : ℝ) / 3200 ≤ (-1281 * q ^ 3 + 7251 * q ^ 2 - 9804 * q + 3888) / 1600 := by
  by_cases hhalf : q ≤ 1 / 2
  · have h := cubic_bernstein_lower (2 * q) (243 / 100) (1127 / 800)
      (4897 / 6400) (5109 / 12800) (1 / 3200)
      (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    nlinarith only [h]
  · by_cases hthree : q ≤ 3 / 4
    · have h := cubic_bernstein_lower (4 * q - 2) (5109 / 12800) (5533 / 25600)
        (5249 / 51200) (4689 / 102400) (1 / 3200)
        (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      nlinarith only [h]
    · by_cases hseven : q ≤ 7 / 8
      · have h := cubic_bernstein_lower (8 * q - 6) (4689 / 102400) (3569 / 204800)
          (269 / 81920) (1473 / 819200) (1 / 3200)
          (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        nlinarith only [h]
      · have h := cubic_bernstein_lower (8 * q - 7) (1473 / 819200) (1 / 3200)
          (147 / 12800) (27 / 800) (1 / 3200)
          (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        nlinarith only [h]

theorem eligibility_threshold_polynomial (q p d : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (_hd : 0 ≤ d) (hd319 : d ≤ 319 / 1600)
    (_hp : 0 ≤ p) (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p)) :
    (1 : ℝ) / 3200 ≤
      (3 - q) * (q - 2) ^ 2 + q * (4 - q) * p +
        (q ^ 3 - 11 * q ^ 2 + 44 * q - 48) * d := by
  let J := q ^ 3 - 11 * q ^ 2 + 44 * q - 48
  have hqterm : 0 ≤ q * (4 - q) := mul_nonneg hq (by linarith)
  have hqterm3 : q * (4 - q) ≤ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ 3 - q by linarith)]
  have hJ : J ≤ -14 := by
    have hfactor : 0 ≤ q ^ 2 - 10 * q + 34 := by nlinarith [sq_nonneg q]
    have := mul_nonpos_of_nonpos_of_nonneg (show q - 1 ≤ 0 by linarith) hfactor
    dsimp [J]
    nlinarith only [this]
  have hpoly := eligibility_threshold_cubic q hq hq1
  by_cases hp11 : 11 / 40 ≤ p
  · have h1 := mul_nonneg hqterm (sub_nonneg.mpr hp11)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd319)
      (show J ≤ 0 by linarith)
    dsimp [J] at *
    nlinarith only [hpoly, h1, h2]
  · have hc : d ≤ p * (1 - p) := by
      rcases hcredit with h | h
      · linarith
      · exact h
    have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) (show J ≤ 0 by linarith)
    have hgap : 0 ≤ 11 / 40 - p := by linarith
    have hsum : 0 ≤ 1 - p - 11 / 40 := by linarith
    have hmonoJ := mul_nonpos_of_nonpos_of_nonneg (show J + 14 ≤ 0 by linarith) hsum
    have hcoef : 0 ≤ -q * (4 - q) - J * (1 - p - 11 / 40) := by
      nlinarith
    have h2 := mul_nonneg hgap hcoef
    dsimp [J] at *
    nlinarith only [hpoly, h1, h2]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (q p d δ w b : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hd : 0 ≤ d) (hd319 : d ≤ 319 / 1600)
    (hp : 0 ≤ p) (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hatt : (3 - q) * w = q * δ + b + 3 * d) :
    0 < 1 - 4 * d - q * δ - (q - q ^ 2 / 4) * (1 - d - δ - w) := by
  have hF := eligibility_threshold_polynomial q p d hq.le hq1 hd hd319 hp hcredit
  have h1 := mul_nonneg (sq_nonneg q) hδ
  have h2 := mul_nonneg (mul_nonneg hq.le
    (show 0 ≤ 4 - q by linarith)) (sub_nonneg.mpr hb)
  have hh := congrArg (fun x : ℝ => q * (4 - q) * x) hatt
  have hid : 4 * (3 - q) *
      (1 - 4 * d - q * δ - (q - q ^ 2 / 4) * (1 - d - δ - w)) =
      ((3 - q) * (q - 2) ^ 2 + q * (4 - q) * p +
        (q ^ 3 - 11 * q ^ 2 + 44 * q - 48) * d) +
        q ^ 2 * δ + q * (4 - q) * (b - (p + d)) := by
    nlinarith only [hh]
  have hpos : 0 < 4 * (3 - q) := by linarith
  nlinarith only [hF, h1, h2, hid, hpos]

end
