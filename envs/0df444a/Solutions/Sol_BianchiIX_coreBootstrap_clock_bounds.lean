-- Prove2me | solution 1 for BianchiIX.coreBootstrap_clock_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:31:31.975453+00:00
-- url     : https://prove2.me/submissions/ebf0adca-c31a-442d-aefc-1c0395dc6978

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

theorem solution {k r u w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    999 / 1000 ≤ coreClockFactor r u w ∧ coreClockFactor r u w ≤ 1 := by
  have hr0 : 0 < r := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hdelta : (u - w) ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 60000 - (u - w) by linarith)
      (show 0 ≤ 1 / 60000 + (u - w) by linarith)]
  have hsmall : (u - w) ^ 2 / r ^ 2 ≤ 1 / 1000 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
    nlinarith [sq_nonneg (r - 5)]
  unfold coreClockFactor
  constructor
  · linarith
  · exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
