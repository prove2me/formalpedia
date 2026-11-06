-- Prove2me | solution 1 for BianchiIX.hasDerivAt_referenceWeakMode
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:56:15.758097+00:00
-- url     : https://prove2.me/submissions/23508b2a-a805-42a0-b886-8c55439a10b8

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Theorems.Thm_BianchiIX_hasDerivAt_referenceTransverseMode
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


theorem solution (k t : ℝ) :
    HasDerivAt (referenceTransverseMode k 2)
      ((-referencePulse k t 0 - 1) * referenceTransverseMode k 2 t) t := by
  convert! hasDerivAt_referenceTransverseMode k 2 t using 1
  dsimp [referencePulse]
  ring
