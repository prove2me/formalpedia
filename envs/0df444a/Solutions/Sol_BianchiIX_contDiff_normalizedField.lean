-- Prove2me | solution 1 for BianchiIX.contDiff_normalizedField
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:54:28.374612+00:00
-- url     : https://prove2.me/submissions/0a1aaf7e-2253-488d-8e29-a003022ae655

import Definitions.Def_BianchiIX_Dynamics_Normalized
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

noncomputable section
open BianchiIX
open Set


theorem solution (n : WithTop ℕ∞) : ContDiff ℝ n normalizedField := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    dsimp [normalizedField, shearPlus, shearMinus, rateOne, rateTwo, rateThree, shearSq, curvature] <;>
    fun_prop
