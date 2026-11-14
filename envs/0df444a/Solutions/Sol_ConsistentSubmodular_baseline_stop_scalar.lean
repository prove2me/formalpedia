-- Prove2me | solution 1 for ConsistentSubmodular.baseline_stop_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:22.946625+00:00
-- url     : https://prove2.me/submissions/2eb33fff-0adc-481f-8328-251c91403fed

import Mathlib

section

theorem solution (A D δ w b q : ℝ)
    (hD : 0 ≤ D) (hDA : D ≤ A) (hδ : 0 ≤ δ) (hb : D ≤ b)
    (hq1 : 1 ≤ q) (hq3 : q ≤ 3 / 2)
    (hatt : (3 - q) * w = q * δ + b + D) :
    0 ≤ w - (q - 1) * δ - D ∧
      2 * A * q - 3 * (A - D) ≤ q * (b + w) := by
  have hq0 : 0 < q := by linarith
  have hden : 0 < 3 - q := by linarith
  have hcoef : 0 ≤ q ^ 2 - 3 * q + 3 := by
    nlinarith [sq_nonneg (q - 3 / 2)]
  have hsuff : 0 ≤ w - (q - 1) * δ - D := by
    have h1 := mul_nonneg hcoef hδ
    have h2 := mul_nonneg (sub_nonneg.mpr hq1) hD
    nlinarith
  refine ⟨hsuff, ?_⟩
  have hlow : 0 ≤ (3 - q) * (b + w) - (5 - q) * D := by
    have h1 := mul_nonneg hq0.le hδ
    have h2 := mul_nonneg (show 0 ≤ 4 - q by linarith) (sub_nonneg.mpr hb)
    nlinarith
  have hg : 0 ≤ (3 - 2 * q) * (3 - q) := by
    exact mul_nonneg (by linarith) hden.le
  have h1 := mul_nonneg (sub_nonneg.mpr hDA) hg
  have h2 := mul_nonneg hD (mul_nonneg hq0.le (sub_nonneg.mpr hq1))
  have h3 := mul_nonneg hq0.le hlow
  nlinarith

end
