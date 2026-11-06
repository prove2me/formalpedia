-- Prove2me | solution 1 for BianchiIX.hasDerivAt_referenceTransverseMode
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:51:03.488104+00:00
-- url     : https://prove2.me/submissions/2ec24762-e602-4e29-b705-ab3f2d41be9a

import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
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


theorem solution (k r t : ℝ) :
    HasDerivAt (referenceTransverseMode k r)
      ((-r + k * Real.tanh (k * t)) * referenceTransverseMode k r t) t := by
  have hz := (hasDerivAt_id t).const_mul k
  have hr := (hasDerivAt_id t).const_mul (-r)
  convert! hr.exp.mul hz.cosh using 1
  dsimp [referenceTransverseMode]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
