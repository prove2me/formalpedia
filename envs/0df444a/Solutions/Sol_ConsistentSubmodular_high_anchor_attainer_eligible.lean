-- Prove2me | solution 1 for ConsistentSubmodular.high_anchor_attainer_eligible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:26.699395+00:00
-- url     : https://prove2.me/submissions/c932f7aa-2d0a-4e63-be40-b504d8b03f7f

import Mathlib

section

namespace ConsistentSubmodular

theorem high_anchor_eligibility_polynomial (q p d : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40)
    (hpd : d ≤ p) :
    0 ≤ (3 - q) * (q - 2) ^ 2 + q * (4 - q) * p +
      (q ^ 3 - 11 * q ^ 2 + 44 * q - 48) * d := by
  let K := q ^ 3 - 12 * q ^ 2 + 48 * q - 48
  have hq : 0 ≤ q := by linarith
  have h4 : 0 ≤ 4 - q := by linarith
  have hC := mul_nonneg (show 0 ≤ 3 - q by linarith) (sq_nonneg (q - 2))
  have hpdterm := mul_nonneg (mul_nonneg hq h4) (sub_nonneg.mpr hpd)
  by_cases hK : 0 ≤ K
  · have := mul_nonneg hK hd
    dsimp [K] at this
    nlinarith only [hC, hpdterm, this]
  · have hqlow : q ≤ 3 / 2 := by
      by_contra hn
      have hs : 0 ≤ q - 3 / 2 := by linarith
      have hf : 0 ≤ q ^ 2 - (21 / 2 : ℝ) * q + 129 / 4 := by
        nlinarith [sq_nonneg q]
      have hp := mul_nonneg hs hf
      dsimp [K] at hK
      nlinarith
    let t := 2 * (q - 1)
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have ht1 : 0 ≤ 1 - t := by dsimp [t]; linarith
    have hid : (3 - q) * (q - 2) ^ 2 + K * (7 / 40) =
        (3 / 40 : ℝ) * (1 - t) ^ 3 + (7 / 80 : ℝ) * t * (1 - t) ^ 2 +
        (89 / 160 : ℝ) * t ^ 2 * (1 - t) + (141 / 320 : ℝ) * t ^ 3 := by
      dsimp [K, t]
      ring
    have hpoly : 0 ≤ (3 - q) * (q - 2) ^ 2 + K * (7 / 40) := by
      rw [hid]
      positivity
    have hdk := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd7) (le_of_not_ge hK)
    dsimp [K] at *
    nlinarith only [hpoly, hdk, hpdterm]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (q p d δ w b : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40)
    (hpd : d ≤ p) (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hatt : (3 - q) * w = q * δ + b + 3 * d) :
    0 ≤ 1 - 4 * d - q * δ - (q - q ^ 2 / 4) * (1 - d - δ - w) := by
  have hF := high_anchor_eligibility_polynomial q p d hq1 hq2 hd hd7 hpd
  have h1 := mul_nonneg (sq_nonneg q) hδ
  have h2 := mul_nonneg (mul_nonneg (show 0 ≤ q by linarith)
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
