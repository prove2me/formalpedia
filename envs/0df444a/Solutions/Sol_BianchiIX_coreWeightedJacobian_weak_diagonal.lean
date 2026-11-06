-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_weak_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:31:16.266004+00:00
-- url     : https://prove2.me/submissions/4cc8a189-4456-4bd3-8753-b7e7d305fc41

import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
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


theorem solution (k z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    let r := y 0
    let u := y 1
    let v := r / Real.cosh z
    let w := y 2 / v
    let d := (coreAuxiliary z y) 1
    let c := (coreAuxiliary z y) 0
    (coreWeightedJacobian k z y) 2 2 =
      -2 * (1 + c) * (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 3 * d ^ 2) -
        2 * u * w / (r * d) := by
  dsimp only
  change -2 * (1 + (coreAuxiliary z y) 0) / (y 0 * (coreAuxiliary z y) 1) -
    2 * y 2 * (y 1 / (y 0 / Real.cosh z)) / (y 0 * (coreAuxiliary z y) 1) +
      2 * y 2 * (1 + (coreAuxiliary z y) 0) *
        (2 * (y 1 - y 2 / (y 0 / Real.cosh z)) / ((y 0 / Real.cosh z) * y 0 ^ 2)) /
        (y 0 * (coreAuxiliary z y) 1 ^ 2) = _
  generalize hc : (coreAuxiliary z y) 0 = c
  field_simp [hr, hd, ne_of_gt (Real.cosh_pos z)]
  dsimp [coreAuxiliary, coreClockFactor]
  field_simp [hr, ne_of_gt (Real.cosh_pos z)]
  ring
