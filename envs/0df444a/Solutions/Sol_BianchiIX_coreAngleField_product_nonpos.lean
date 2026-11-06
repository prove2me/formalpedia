-- Prove2me | solution 1 for BianchiIX.coreAngleField_product_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:03:13.509892+00:00
-- url     : https://prove2.me/submissions/0498f428-63f4-4f5d-9ea1-660aa88ee42d

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.coreBootstrap_coupling_nonneg {k u v w : ℝ} (hk : 6 ≤ k) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w) : 0 ≤ coupling u v w := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  exact mul_nonneg hu.1 (by linarith)

end
end

theorem solution {k z : ℝ} {y : CoreAngleState} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ y 0) (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    coreAngleField z y 2 ≤ 0 := by
  have hr0 : 0 < y 0 := by linarith
  have hv0 : 0 < y 0 / Real.cosh z := lt_of_lt_of_le zero_lt_one hv
  have hp : 0 ≤ y 2 := by
    have H := mul_nonneg hw.1 hv0.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hv0)] using H
  have hC := coreBootstrap_coupling_nonneg hk hv hu hw.1
  have hd := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
    (coreBootstrap_clock_bounds hk hr hu hw).1
  dsimp [coreAngleField]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hp) (by linarith)
  · exact (mul_pos hr0 hd).le
