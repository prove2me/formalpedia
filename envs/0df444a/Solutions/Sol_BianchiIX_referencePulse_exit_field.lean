-- Prove2me | solution 1 for BianchiIX.referencePulse_exit_field
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:55:50.099903+00:00
-- url     : https://prove2.me/submissions/2b50c143-96b3-499e-9b94-c18fe66c7075

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Theorems.Thm_BianchiIX_referencePulse_exit
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set


theorem solution {k : ℝ} (hk : 1 < k) :
    projectiveField (referencePulse k (referenceHalfTime k)) =
      ![-1, 0, -Real.sqrt (k ^ 2 - 1), 0] := by
  rw [referencePulse_exit hk]
  ext i
  fin_cases i <;>
    dsimp [projectiveField, phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling] <;>
    ring
