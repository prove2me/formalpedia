-- Prove2me | solution 1 for BianchiIX.referenceNormalizedTime_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:50:11.384465+00:00
-- url     : https://prove2.me/submissions/4ce1389d-e929-48bc-a540-f449d6c2b77a

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
    0 < referenceNormalizedTime k := by
  exact div_pos (mul_pos (by positivity) (Real.arcosh_pos hk))
    (mul_pos (by norm_num) (lt_trans zero_lt_one hk))
