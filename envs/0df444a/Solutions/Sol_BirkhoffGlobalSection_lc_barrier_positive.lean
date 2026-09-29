-- Prove2me | solution 1 for BirkhoffGlobalSection.lc_barrier_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:01:49.490747+00:00
-- url     : https://prove2.me/submissions/990674a7-4043-4cd0-b460-099840bebdd5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (μ c z₁ z₂ r : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2) (hc0 : 21 / 10 ≤ c)
    (hz : 2 * (z₁ ^ 2 + z₂ ^ 2) = (3 - 2 * μ) / 5)
    (hr : 0 < r) (hr2 : r ^ 2 = (2 * (z₁ ^ 2 - z₂ ^ 2) - 1) ^ 2 + (4 * z₁ * z₂) ^ 2) :
    (1 - μ) / 2 <
      (c - (2 * (z₁ ^ 2 + z₂ ^ 2) - μ) ^ 2 / 2 - μ / r) * z₁ ^ 2
        + (c - (2 * (z₁ ^ 2 + z₂ ^ 2) + μ) ^ 2 / 2 - μ / r) * z₂ ^ 2 := by
  -- With `d = (3-2μ)/5`, `ρ = d/2`,
  -- `r₀ = 1 - d`, one has `r₀ ≤ r ≤ 1 + d` and
  -- `2 r r₀ (RHS - (1-μ)/2) = 2 r (p(μ)/1250 + r₀ ρ (c - 21/10)) + μ ρ (r - r₀) W`
  -- with `p > 0` (explicit SOS) and `W ≥ 0`.
  have hr0 : 0 < 2 * (1 + μ) / 5 := by linarith
  have hlo2 : r ^ 2 - (2 * (1 + μ) / 5) ^ 2 = 8 * z₂ ^ 2 := by
    linear_combination (-2 * μ / 5 + 2 * z₁ ^ 2 + 2 * z₂ ^ 2 - 7 / 5) * hz + hr2
  have hhi2 : ((8 - 2 * μ) / 5) ^ 2 - r ^ 2 = 8 * z₁ ^ 2 := by
    linear_combination (2 * μ / 5 - 2 * z₁ ^ 2 - 2 * z₂ ^ 2 - 13 / 5) * hz - hr2
  have hlo : 2 * (1 + μ) / 5 ≤ r := by
    have e : (r - 2 * (1 + μ) / 5) * (r + 2 * (1 + μ) / 5) = 8 * z₂ ^ 2 := by
      linear_combination hlo2
    have h := (mul_nonneg_iff_of_pos_right (by linarith : 0 < r + 2 * (1 + μ) / 5)).mp
      (by rw [e]; positivity)
    linarith
  have hhi : r ≤ (8 - 2 * μ) / 5 := by
    have e : ((8 - 2 * μ) / 5 - r) * ((8 - 2 * μ) / 5 + r) = 8 * z₁ ^ 2 := by
      linear_combination hhi2
    have h := (mul_nonneg_iff_of_pos_right (by linarith : 0 < (8 - 2 * μ) / 5 + r)).mp
      (by rw [e]; positivity)
    linarith
  have hp : 0 < 98 * μ ^ 4 - 133 * μ ^ 3 + 203 * μ ^ 2 - 153 * μ + 38 := by
    have e : 98 * μ ^ 4 - 133 * μ ^ 3 + 203 * μ ^ 2 - 153 * μ + 38 =
        98 * (μ ^ 2 - 19 / 28 * μ + 1 / 10) ^ 2 + 5531 / 40 * (μ - 2794 / 5531) ^ 2
          + 239918 / 138275 := by ring
    rw [e]; positivity
  have hmr : μ / r * r = μ := div_mul_cancel₀ μ hr.ne'
  have hkey :
      2 * r * (2 * (1 + μ) / 5) *
          ((c - (2 * (z₁ ^ 2 + z₂ ^ 2) - μ) ^ 2 / 2 - μ / r) * z₁ ^ 2
            + (c - (2 * (z₁ ^ 2 + z₂ ^ 2) + μ) ^ 2 / 2 - μ / r) * z₂ ^ 2 - (1 - μ) / 2) =
        2 * r * ((98 * μ ^ 4 - 133 * μ ^ 3 + 203 * μ ^ 2 - 153 * μ + 38) / 1250
            + 2 * (1 + μ) / 5 * ((3 - 2 * μ) / 10) * (c - 21 / 10))
          + μ * ((3 - 2 * μ) / 10) * (r - 2 * (1 + μ) / 5) *
            (r * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r) + 2 * ((3 - 2 * μ) / 5) ^ 2
              + 2 * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r)) := by
    linear_combination
      (-(μ + 1) * (-50 * c * r - 4 * μ ^ 3 * r + 20 * μ ^ 2 * r * z₁ ^ 2
        + 20 * μ ^ 2 * r * z₂ ^ 2 + 41 * μ ^ 2 * r - 150 * μ * r * z₁ ^ 2
        + 50 * μ * r * z₂ ^ 2 - 21 * μ * r + 50 * μ + 100 * r * z₁ ^ 4
        + 200 * r * z₁ ^ 2 * z₂ ^ 2 + 30 * r * z₁ ^ 2 + 100 * r * z₂ ^ 4
        + 30 * r * z₂ ^ 2 + 9 * r) / 125) * hz
      + (-μ * r * (μ + 1) * (2 * μ - 3) / 25) * hr2
      + (-2 * (2 * (1 + μ) / 5) * (z₁ ^ 2 + z₂ ^ 2)) * hmr
  have hgap : 0 ≤ 1 + (3 - 2 * μ) / 5 - r := by linarith
  have hW : 0 ≤ r * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r)
      + 2 * ((3 - 2 * μ) / 5) ^ 2 + 2 * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r) := by
    positivity
  have hrhs : 0 < 2 * r * ((98 * μ ^ 4 - 133 * μ ^ 3 + 203 * μ ^ 2 - 153 * μ + 38) / 1250
            + 2 * (1 + μ) / 5 * ((3 - 2 * μ) / 10) * (c - 21 / 10))
          + μ * ((3 - 2 * μ) / 10) * (r - 2 * (1 + μ) / 5) *
            (r * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r) + 2 * ((3 - 2 * μ) / 5) ^ 2
              + 2 * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r)) := by
    have h1 : 0 < 2 * r * ((98 * μ ^ 4 - 133 * μ ^ 3 + 203 * μ ^ 2 - 153 * μ + 38) / 1250
        + 2 * (1 + μ) / 5 * ((3 - 2 * μ) / 10) * (c - 21 / 10)) := by
      have : 0 ≤ 2 * (1 + μ) / 5 * ((3 - 2 * μ) / 10) * (c - 21 / 10) := by
        have : 0 ≤ (3 - 2 * μ) / 10 := by linarith
        have : 0 ≤ c - 21 / 10 := by linarith
        positivity
      have : 0 < (98 * μ ^ 4 - 133 * μ ^ 3 + 203 * μ ^ 2 - 153 * μ + 38) / 1250 := by
        positivity
      positivity
    have h2 : 0 ≤ μ * ((3 - 2 * μ) / 10) * (r - 2 * (1 + μ) / 5) *
        (r * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r) + 2 * ((3 - 2 * μ) / 5) ^ 2
          + 2 * (2 * (1 + μ) / 5) * (1 + (3 - 2 * μ) / 5 - r)) := by
      have : 0 ≤ (3 - 2 * μ) / 10 := by linarith
      have : 0 ≤ r - 2 * (1 + μ) / 5 := by linarith
      positivity
    linarith
  rw [← hkey] at hrhs
  have hpos : 0 < 2 * r * (2 * (1 + μ) / 5) := by positivity
  have := (pos_iff_pos_of_mul_pos hrhs).mp hpos
  linarith
