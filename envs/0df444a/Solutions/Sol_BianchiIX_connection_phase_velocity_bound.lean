-- Prove2me | solution 1 for BianchiIX.connection_phase_velocity_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:44:33.982201+00:00
-- url     : https://prove2.me/submissions/7ef236b2-3abc-455a-8580-a764e2c9e503

import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
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

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

private theorem BianchiIX.connection_coupling_nonneg {u v w : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huv : u ≤ v) : 0 ≤ coupling u v w := by
  unfold coupling
  exact mul_nonneg hu (by linarith only [hw, huv])

theorem solution {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    |phaseVelocity (-m) u v w| ≤ v ^ 2 + w ^ 2 + 3 * μ * u := by
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hc := connection_coupling_nonneg hu.1 hw.1 huv
  have hmc₀ := mul_nonneg hm0 hc
  have hmc₁ := mul_le_mul_of_nonneg_left (connection_coupling_bounds hu.1 hv hw).2 hm0
  have hdiff : -1 ≤ v - w ∧ v - w ≤ 1 := by constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2]
  have hd₀ := mul_le_mul_of_nonneg_left hdiff.1 hu.1
  have hd₁ := mul_le_mul_of_nonneg_left hdiff.2 hu.1
  have hcoeff := mul_le_mul_of_nonneg_right
    (show 1 + 2 * m ≤ 3 * μ by linarith only [(abs_le.mp hm).2, hμ]) hu.1
  rw [abs_le]
  dsimp [phaseVelocity]
  constructor <;> nlinarith only [hmc₀, hmc₁, hd₀, hd₁, hcoeff, sq_nonneg v, sq_nonneg w]
