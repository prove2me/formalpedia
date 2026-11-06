-- Prove2me | solution 1 for BianchiIX.referencePulse_above_section
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:49:45.524176+00:00
-- url     : https://prove2.me/submissions/b54dbd20-2055-4230-b5c3-dfb11fc6aad4

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


theorem solution {k t : ℝ} (hk : 1 < k)
    (ht : t ∈ Ioo (-referenceHalfTime k) (referenceHalfTime k)) :
    1 < referencePulse k t 2 := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hkt : |k * t| < Real.arcosh k := by
    apply abs_lt.mpr
    constructor
    · have h := mul_lt_mul_of_pos_left ht.1 hk0
      simpa [referenceHalfTime, mul_div_cancel₀ _ (ne_of_gt hk0)] using h
    · have h := mul_lt_mul_of_pos_left ht.2 hk0
      simpa [referenceHalfTime, mul_div_cancel₀ _ (ne_of_gt hk0)] using h
  have hc : Real.cosh (k * t) < k := by
    calc
      Real.cosh (k * t) < Real.cosh (Real.arcosh k) :=
        Real.cosh_lt_cosh.mpr (by simpa only [abs_of_pos (Real.arcosh_pos hk)] using hkt)
      _ = k := Real.cosh_arcosh hk.le
  exact (one_lt_div (Real.cosh_pos _)).mpr hc
