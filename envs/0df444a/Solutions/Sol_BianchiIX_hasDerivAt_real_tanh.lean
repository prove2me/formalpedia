-- Prove2me | solution 1 for BianchiIX.hasDerivAt_real_tanh
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:46:30.778028+00:00
-- url     : https://prove2.me/submissions/6e349a67-3268-4149-97fb-b0bc19bacf10

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
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

noncomputable section
open BianchiIX


theorem solution (z : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh z ^ 2) z := by
  convert! (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z)
    (ne_of_gt (Real.cosh_pos z)) using 1
  · ext x
    exact Real.tanh_eq_sinh_div_cosh x
  · rw [← pow_two, ← pow_two, Real.cosh_sq_sub_sinh_sq]
