-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.optimal_quantity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:28:46.531692+00:00
-- url     : https://prove2.me/submissions/5d2e745f-a643-4445-aca8-4da615580f3a

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory
open CarbonPolicy.TaxVsCap

theorem solution(b w γ a k : ℝ) (hb : 0 < b) :
    ∀ q : ℝ, profit b w γ a k q ≤ profit b w γ a k (qStar b γ a k) := by
  intro q
  have hb' : b ≠ 0 := hb.ne'
  unfold profit qStar
  have key : (a - b * ((a - γ * k) / (2 * b))) * ((a - γ * k) / (2 * b)) - (γ * ((a - γ * k) / (2 * b)) - w) * k
      - ((a - b * q) * q - (γ * q - w) * k) = b * (q - (a - γ * k) / (2 * b)) ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg hb.le (sq_nonneg (q - (a - γ * k) / (2 * b)))]
