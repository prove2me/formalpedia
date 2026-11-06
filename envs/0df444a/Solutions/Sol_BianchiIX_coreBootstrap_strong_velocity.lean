-- Prove2me | solution 1 for BianchiIX.coreBootstrap_strong_velocity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:02:24.104913+00:00
-- url     : https://prove2.me/submissions/a742c541-f3de-4205-bffe-574e6e84dfcb

import Definitions.Def_BianchiIX_Algebra_Projective
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_component_bounds (m v : ℝ) :
    |m - 1| ≤ coreRadius m v ∧ |v| ≤ coreRadius m v := by
  have hr : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg v]
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (m - 1)]

end
end

theorem solution {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m v ∧ coreRadius m v ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k)
    (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    strongVelocity m u v w ≤ (-k ^ 2 / 10) * u := by
  have hm := (abs_le.mp ((coreRadius_component_bounds m v).1.trans hr.2)).1
  have hvhi : v ≤ 101 / 100 * k :=
    (le_abs_self v).trans ((coreRadius_component_bounds m v).2.trans hr.2)
  have hr2 : (99 / 100 * k) ^ 2 ≤ coreRadius m v ^ 2 :=
    (sq_le_sq₀ (by linarith) (by exact Real.sqrt_nonneg _)).mpr hr.1
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hu2 := (sq_le_sq₀ hu.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)).mpr hu'
  have hvw := mul_le_mul hvhi hw' hw.1 (by linarith : 0 ≤ 101 / 100 * k)
  have hbase : 1 - m ^ 2 - (v - w) ^ 2 + u ^ 2 ≤ -k ^ 2 / 5 := by
    nlinarith [sq_nonneg (k - 6), sq_nonneg w]
  have H := mul_le_mul_of_nonneg_right hbase hu.1
  unfold strongVelocity
  nlinarith
