-- Prove2me | solution 1 for CachonPushPull.ShippingCost.prebook_positive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:42:34.701298+00:00
-- url     : https://prove2.me/submissions/d3d78197-04f9-4a27-b743-963302696e81

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

theorem aux_pbpos_rhs_pos (v w₁ w₂ : ℝ) (hvw₁ : v < w₁) (hw₁₂ : w₁ < w₂) :
    0 < (w₂ - w₁) / (w₂ - v) :=
  div_pos (by linarith) (by linarith)

end CachonPushPull.ShippingCost

open CachonPushPull.ShippingCost
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hvw₁ : v < w₁) (hw₁₂ : w₁ < w₂) (hw₂p : w₂ ≤ p)
    (yr : ℝ) (hyr : cdf μ yr = (w₂ - w₁) / (w₂ - v)) :
    0 < yr := by
  by_contra h
  have h1 : cdf μ yr ≤ cdf μ 0 := monotone_cdf μ (not_lt.mp h)
  rw [hD.cdf_zero, hyr] at h1
  have h2 := aux_pbpos_rhs_pos v w₁ w₂ hvw₁ hw₁₂
  linarith
