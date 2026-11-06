-- Prove2me | solution 1 for BianchiIX.coreBootstrap_original_clock_lower
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:06:50.929283+00:00
-- url     : https://prove2.me/submissions/b60f0b32-9c45-4133-931b-d41c7c880e44

import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_inverse_scale_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


/-- A uniform lower bound on the angle speed in the original normalized Einstein time. -/
theorem solution {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m v ∧ coreRadius m v ≤ 101 / 100 * k)
    (hv : 0 ≤ v) (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k)
    (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    1 / k ≤ (6 / projectiveDenom m u v w) * coreRadius m v * coreClockFactor (coreRadius m v) u w := by
  have hk0 : 0 < k := by linarith
  have hDlo := coreBootstrap_denom_lower (m := m) (v := v) hk hu hw
  have hA := (coreBootstrap_inverse_scale_bounds hk hr.2 hv hu hw).1
  have hd := coreBootstrap_clock_bounds hk hr.1 hu hw
  have hrd : k / 2 ≤ coreRadius m v * coreClockFactor (coreRadius m v) u w := by
    have H := mul_le_mul hr.1 hd.1 (by norm_num : (0 : ℝ) ≤ 999 / 1000) (by linarith)
    nlinarith
  calc
    1 / k ≤ (3 / k ^ 2) * (k / 2) := by
      field_simp
      nlinarith
    _ ≤ (6 / projectiveDenom m u v w) *
        (coreRadius m v * coreClockFactor (coreRadius m v) u w) :=
      mul_le_mul hA hrd (by positivity) (by positivity)
    _ = _ := by ring
