-- Prove2me | solution 1 for BianchiIX.coreBootstrap_denom_upper
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:00:57.473729+00:00
-- url     : https://prove2.me/submissions/e0910b65-ff63-4edc-8ab1-941435305b4b

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
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

theorem solution {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k) (hv : 0 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    projectiveDenom m u v w ≤ 2 * k ^ 2 := by
  have hm : m - 1 ≤ 101 / 100 * k :=
    (le_abs_self _).trans ((coreRadius_component_bounds m v).1.trans hr)
  have hr2 := (sq_le_sq₀ (Real.sqrt_nonneg (coreEnergy m v)) (by linarith)).mpr hr
  change coreRadius m v ^ 2 ≤ (101 / 100 * k) ^ 2 at hr2
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hdelta : (u - w) ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 60000 - (u - w) by linarith)
      (show 0 ≤ 1 / 60000 + (u - w) by linarith)]
  have hprod := mul_nonneg hv (add_nonneg hu.1 hw.1)
  unfold projectiveDenom curvature
  nlinarith [sq_nonneg (k - 6)]
