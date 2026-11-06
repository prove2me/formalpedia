-- Prove2me | solution 1 for BianchiIX.connection_denom_upper
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:44:37.05911+00:00
-- url     : https://prove2.me/submissions/4c6ee4a7-42f9-4d09-9076-6d0a01e7b028

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


theorem solution {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    projectiveDenom (-m) u v w ≤ 2 * μ ^ 2 := by
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 : m ^ 2 ≤ (μ + 1 / 2) ^ 2 :=
    pow_le_pow_left₀ hm0 (by linarith only [(abs_le.mp hm).2]) 2
  have hu2 : u ^ 2 ≤ 1 := by
    have H := pow_le_pow_left₀ hu.1 hu.2 2
    norm_num at H
    linarith only [H]
  have hv2 : v ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hv.1 hv.2 2
  have hw2 : w ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hw.1 hw.2 2
  dsimp [projectiveDenom, curvature]
  nlinarith only [hm2, hu2, hv2, hw2, mul_nonneg hu.1 hv.1, mul_nonneg hv.1 hw.1,
    mul_nonneg hw.1 hu.1, sq_nonneg (μ - 4), hμ]
