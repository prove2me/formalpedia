-- Prove2me | solution 1 for BianchiIX.connectionLogField_components
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:48:25.266208+00:00
-- url     : https://prove2.me/submissions/c0106612-18e0-486f-8954-e7ef5be77658

import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
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


theorem solution {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    connectionLogField y 0 = phaseVelocity (y 0) (y 1) (y 2) (y 3) / connectionClockRate y ∧
    connectionLogField y 1 = connectionStrongRate (-y 0) (y 1) (y 2) (y 3) /
      connectionClockRate y * y 1 ∧
    connectionLogField y 2 = (y 0 - 1 - coupling (y 1) (y 2) (y 3)) /
      connectionClockRate y * y 2 ∧
    connectionLogField y 3 = y 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (connectionClockRate y)⁻¹ * phaseVelocity _ _ _ _ = _
    ring
  · change (connectionClockRate y)⁻¹ * strongVelocity _ _ _ _ = _
    dsimp [strongVelocity, connectionStrongRate]
    ring
  · change (connectionClockRate y)⁻¹ * activeVelocity _ _ _ _ = _
    dsimp [activeVelocity]
    ring
  · change (connectionClockRate y)⁻¹ * (connectionClockRate y * y 3) = y 3
    rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul]
