-- Prove2me | solution 1 for CramerChernoff.gaussian_exponent_optimal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T02:26:00.703241+00:00
-- url     : https://prove2.me/submissions/cbb1abd7-d3de-493a-afd4-29d0da4543e1

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real

theorem solution (C t lam : ℝ) (hC : 0 < C) :
    - t ^ 2 / (4 * C) ≤ C * lam ^ 2 - lam * t := by
  have hsq : C * (lam - t / (2 * C)) ^ 2 ≥ 0 := by positivity
  have h2C : (2 * C) ≠ 0 := by positivity
  have hkey : C * lam ^ 2 - lam * t = C * (lam - t / (2 * C)) ^ 2 - t ^ 2 / (4 * C) := by
    field_simp; ring
  have hneg : - t ^ 2 / (4 * C) = - (t ^ 2 / (4 * C)) := by ring
  rw [hkey, hneg]; linarith [hsq]
