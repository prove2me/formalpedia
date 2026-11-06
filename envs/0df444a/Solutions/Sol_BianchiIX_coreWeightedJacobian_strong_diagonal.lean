-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_strong_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:30:39.554363+00:00
-- url     : https://prove2.me/submissions/a9de8ecb-f9e8-4ece-9409-811078a895b1

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


/-- Combining the clock derivative with the diagonal retains its negative sign. -/
theorem solution (k z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    let r := y 0
    let u := y 1
    let w := y 2 / (r / Real.cosh z)
    let d := (coreAuxiliary z y) 1
    let a := (coreAuxiliary z y) 2
    (coreWeightedJacobian k z y) 1 1 =
      a * (r ^ 2 + u ^ 2 - w ^ 2) / (r ^ 2 * d ^ 2) + u ^ 2 / (r * d) := by
  dsimp only
  change (coreAuxiliary z y) 2 / (coreAuxiliary z y) 1 +
    y 1 * (y 1 / y 0) / (coreAuxiliary z y) 1 - y 1 * (coreAuxiliary z y) 2 *
      (-2 * (y 1 - y 2 / (y 0 / Real.cosh z)) / y 0 ^ 2) / (coreAuxiliary z y) 1 ^ 2 = _
  generalize ha : (coreAuxiliary z y) 2 = a
  field_simp [hr, hd]
  dsimp [coreAuxiliary, coreClockFactor]
  field_simp [hr]
  ring
