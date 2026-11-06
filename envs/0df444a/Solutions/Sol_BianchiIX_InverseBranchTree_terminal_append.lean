-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.terminal_append
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:02:11.030037+00:00
-- url     : https://prove2.me/submissions/f240d9f0-4f04-4c7e-b5c0-092fe1d0636e

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim


open Set MeasureTheory
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


@[simp] theorem solution (w : List ℕ+) (a : ℕ+) :
    T.terminal (w ++ [a]) = T.domain w a ∩ T.branch w a ⁻¹' T.terminal w := by
  simp [terminal, List.reverseRecOn]
