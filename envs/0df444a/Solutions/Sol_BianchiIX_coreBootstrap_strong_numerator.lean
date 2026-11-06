-- Prove2me | solution 1 for BianchiIX.coreBootstrap_strong_numerator
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:31:47.536244+00:00
-- url     : https://prove2.me/submissions/ef8e65c8-d51d-4f98-a142-8d29ceea2094

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

/-- The strong-wall logarithmic numerator retains a negative term of order k. -/
theorem solution {k r u v w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r) (hv : v ≤ r) (hc : -1 ≤ c)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    -r / 2 - c + (v / r) * w + (u ^ 2 - w ^ 2) / (2 * r) ≤ -3 * k / 10 := by
  have hr0 : 0 < r := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hvw : v / r * w ≤ w := by
    have H := mul_le_mul_of_nonneg_right ((div_le_one hr0).mpr hv) hw.1
    simpa only [one_mul] using H
  have hu2 : u ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := (sq_le_sq₀ hu.1 (by norm_num)).mpr hu'
  have he : (u ^ 2 - w ^ 2) / (2 * r) ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg w]
  linarith
