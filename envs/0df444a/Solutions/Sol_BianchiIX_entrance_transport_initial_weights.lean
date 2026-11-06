-- Prove2me | solution 1 for BianchiIX.entrance_transport_initial_weights
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:59:56.733634+00:00
-- url     : https://prove2.me/submissions/60b08bfa-4839-4baf-b72a-50b7649be6a0

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {u v w θ k βU βW : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w ∧ w ≤ 1) (hθ : 0 ≤ θ)
    (hk : 1 ≤ k) (hU : |βU| ≤ 12 * k) (hW : |βW| ≤ 9) :
    |u * βU| + |w * βW| ≤ 12 * k * u + 9 * w ∧
      (v * |u * βU| + (u * v + θ * v ^ 2 * w) * |w * βW|) / k ≤
        21 * (u * v + θ * (v * w) ^ 2) := by
  have hk0 : 0 < k := by linarith
  let H := u * v + θ * (v * w) ^ 2
  let S := u * v + θ * v ^ 2 * w
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity [hw.1]
  have hU' : |u * βU| ≤ 12 * k * u := by
    rw [abs_mul, abs_of_nonneg hu]
    exact (mul_le_mul_of_nonneg_left hU hu).trans_eq (by ring)
  have hW' : |w * βW| ≤ 9 * w := by
    rw [abs_mul, abs_of_nonneg hw.1]
    exact (mul_le_mul_of_nonneg_left hW hw.1).trans_eq (by ring)
  refine ⟨add_le_add hU' hW', ?_⟩
  have hP : u * v ≤ H := by dsimp [H]; nlinarith only [mul_nonneg hθ (sq_nonneg (v * w))]
  have hSW : S * w ≤ H := by
    have HE := mul_le_of_le_one_right (mul_nonneg hu hv) hw.2
    dsimp [S, H]
    nlinarith only [HE]
  apply (div_le_iff₀ hk0).mpr
  have HE := add_le_add (mul_le_mul_of_nonneg_left hU' hv) (mul_le_mul_of_nonneg_left hW' hS)
  change _ ≤ 21 * H * k
  calc
    _ ≤ v * (12 * k * u) + S * (9 * w) := HE
    _ = 12 * k * (u * v) + 9 * (S * w) := by ring
    _ ≤ 12 * k * H + 9 * H := add_le_add (mul_le_mul_of_nonneg_left hP (by positivity))
      (mul_le_mul_of_nonneg_left hSW (by norm_num))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hk hH]
