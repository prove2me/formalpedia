-- Prove2me | solution 1 for AvramDividend.Classical.positive_midpoint_multiplicative_of_ratio_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:23:51.190565+00:00
-- url     : https://prove2.me/submissions/e4645267-60a3-4f71-8488-eaf749da0144

import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
theorem solution
    (f : ℝ → ℝ)
    (hfpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hratio : ∀ x y t : ℝ, 0 < x → x ≤ y → 0 < t →
      f x / f (x + t) ≤ f y / f (y + t)) :
    ∀ x y : ℝ, 0 < x → x < y →
      f x * f y ≤ (f ((x + y) / 2)) ^ 2 := by
  intro x y hx hxy
  have h := hratio x ((x + y) / 2) ((y - x) / 2) hx (by linarith) (by linarith)
  have e1 : x + (y - x) / 2 = (x + y) / 2 := by ring
  have e2 : (x + y) / 2 + (y - x) / 2 = y := by ring
  rw [e1, e2, div_le_div_iff₀ (hfpos _ (by linarith)) (hfpos _ (by linarith))] at h
  nlinarith [h]
