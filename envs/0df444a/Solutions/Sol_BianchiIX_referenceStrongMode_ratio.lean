-- Prove2me | solution 1 for BianchiIX.referenceStrongMode_ratio
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:56:41.592696+00:00
-- url     : https://prove2.me/submissions/e07d4a28-a05d-4dfa-ba01-2aeb145a6bb4

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Theorems.Thm_BianchiIX_referenceTransverseMode_ratio
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
    referenceTransverseMode k (k ^ 2 / 2) (referenceHalfTime k) /
      referenceTransverseMode k (k ^ 2 / 2) (-referenceHalfTime k) =
      Real.exp (-k * Real.arcosh k) := by
  rw [referenceTransverseMode_ratio]
  congr 1
  unfold referenceHalfTime
  field_simp [ne_of_gt (lt_trans zero_lt_one hk)]
