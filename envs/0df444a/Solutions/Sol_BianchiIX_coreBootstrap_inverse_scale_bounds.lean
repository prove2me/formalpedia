-- Prove2me | solution 1 for BianchiIX.coreBootstrap_inverse_scale_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:04:24.944539+00:00
-- url     : https://prove2.me/submissions/de8c94b2-4655-4cb4-8972-2d0f7c748562

import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_denom_upper
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


theorem solution {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k)
    (hv : 0 ≤ v) (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k)
    (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    3 / k ^ 2 ≤ 6 / projectiveDenom m u v w ∧ 6 / projectiveDenom m u v w ≤ 3 := by
  have hk0 : 0 < k := by linarith
  have hDlo := coreBootstrap_denom_lower (m := m) (v := v) hk hu hw
  have hDhi := coreBootstrap_denom_upper hk hr hv hu hw
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (by linarith)).mpr
    nlinarith
  · apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
