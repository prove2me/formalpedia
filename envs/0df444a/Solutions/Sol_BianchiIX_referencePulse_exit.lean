-- Prove2me | solution 1 for BianchiIX.referencePulse_exit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:48:53.829789+00:00
-- url     : https://prove2.me/submissions/12829810-70be-4027-b5fd-8fbdf11b919b

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
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
open Set MeasureTheory


theorem solution {k : ℝ} (hk : 1 < k) :
    referencePulse k (referenceHalfTime k) = ![1 - Real.sqrt (k ^ 2 - 1), 0, 1, 0] := by
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  simp only [referencePulse, referenceHalfTime, mul_div_cancel₀ _ hk0,
    Real.tanh_arcosh hk.le, Real.cosh_arcosh hk.le, div_self hk0]
