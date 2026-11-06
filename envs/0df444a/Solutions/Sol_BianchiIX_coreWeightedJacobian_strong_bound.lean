-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_strong_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:42:24.545269+00:00
-- url     : https://prove2.me/submissions/2a9789c1-8c90-433b-a412-9777e0426d76

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_diagonal_factors
import Theorems.Thm_BianchiIX_coreBootstrap_strong_numerator
import Theorems.Thm_BianchiIX_coreWeightedJacobian_strong_diagonal
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_strong_diagonal {k r u w a : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (ha : a ≤ -3 * k / 10) :
    a * (r ^ 2 + u ^ 2 - w ^ 2) / (r ^ 2 * coreClockFactor r u w ^ 2) +
      u ^ 2 / (r * coreClockFactor r u w) ≤ -k / 4 := by
  obtain ⟨hq, _, he⟩ := coreBootstrap_diagonal_factors hk hr hu hw
  have H := mul_le_mul_of_nonpos_left hq (show a ≤ 0 by linarith)
  rw [← mul_div_assoc] at H
  nlinarith

theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    (coreWeightedJacobian k z y) 1 1 ≤ -k / 4 := by
  have hr0 : 0 < y 0 := by linarith
  have hd : (coreAuxiliary z y) 1 ≠ 0 := by
    have H := (coreBootstrap_clock_bounds hk hr hu hw).1
    change 999 / 1000 ≤ (coreAuxiliary z y) 1 at H
    linarith
  have hv : y 0 / Real.cosh z ≤ y 0 := div_le_self hr0.le (Real.one_le_cosh z)
  have hc : -1 ≤ -Real.tanh z := by linarith [Real.tanh_lt_one z]
  have ha : (coreAuxiliary z y) 2 ≤ -3 * k / 10 := by
    have H := coreBootstrap_strong_numerator hk hr hv hc hu hw
    convert! H using 1
    dsimp [coreAuxiliary]
    field_simp [ne_of_gt hr0]
    ring
  rw [coreWeightedJacobian_strong_diagonal k z (ne_of_gt hr0) hd]
  exact coreBootstrap_strong_diagonal hk hr hu hw ha
