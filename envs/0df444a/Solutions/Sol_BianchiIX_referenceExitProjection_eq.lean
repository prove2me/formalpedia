-- Prove2me | solution 1 for BianchiIX.referenceExitProjection_eq
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:59:38.320596+00:00
-- url     : https://prove2.me/submissions/35d515da-14ea-46a3-bd8c-98c590b61ecb

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Theorems.Thm_BianchiIX_referenceCoreGap_pos
import Theorems.Thm_BianchiIX_referencePulse_exit_field
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


theorem solution {k : ℝ} (hk : 1 < k) (xi : ProjectiveState) :
    referenceExitProjection k xi = xi -
      (xi 2 / projectiveField (referencePulse k (referenceHalfTime k)) 2) •
        projectiveField (referencePulse k (referenceHalfTime k)) := by
  rw [referencePulse_exit_field hk]
  have hd := ne_of_gt (referenceCoreGap_pos hk)
  ext i
  fin_cases i <;> dsimp [referenceExitProjection] <;> field_simp [hd] <;> ring
