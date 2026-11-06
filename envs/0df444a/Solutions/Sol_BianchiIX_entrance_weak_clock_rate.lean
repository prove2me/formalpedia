-- Prove2me | solution 1 for BianchiIX.entrance_weak_clock_rate
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:44:45.250503+00:00
-- url     : https://prove2.me/submissions/c0b9336a-a8b1-42c1-b7c9-9091ea2d6fe7

import Definitions.Def_BianchiIX_Algebra_Projective
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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX

section
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

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_clock_identities {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    (-m - 1 - coupling u v w) / connectionSpeed m u v w =
      -1 - 2 * (1 + coupling u v w) / connectionSpeed m u v w ∧
    connectionStrongRate m u v w / connectionSpeed m u v w + (m + 1) / 2 =
      (-(v - w) ^ 2 + u ^ 2 - (m + 1) * coupling u v w) / (2 * connectionSpeed m u v w) := by
  constructor <;> dsimp [connectionSpeed, connectionStrongRate] at * <;> field_simp <;> ring

end
end

private theorem BianchiIX.entrance_speed_bounds {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    3 / 4 * k ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ 21 / 20 * k := by
  have hC := connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hm.1, hm.2, hC.1, hC.2, hu.2, hu2, hk]

theorem solution {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    (-m - 1 - coupling u v w) / connectionSpeed m u v w ≤ -(1 + 1 / k) := by
  have hk0 : 0 < k := by linarith
  have hD := entrance_speed_bounds hk hm hu hv hw
  have hD0 : 0 < connectionSpeed m u v w := by linarith [hD.1]
  have hC := (connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩).1
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hCu := mul_le_mul_of_nonneg_left hC hk0.le
  have hku := mul_le_mul_of_nonneg_left hu2 hk0.le
  have hfrac : 1 / k ≤ 2 * (1 + coupling u v w) / connectionSpeed m u v w := by
    apply (div_le_div_iff₀ hk0 hD0).mpr
    nlinarith only [hCu, hku, hD.2, hk0]
  have hid := (connection_clock_identities hD0.ne').1
  linarith only [hid, hfrac]
