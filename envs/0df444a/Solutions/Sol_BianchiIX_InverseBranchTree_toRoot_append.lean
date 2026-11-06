-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.toRoot_append
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:02:55.710583+00:00
-- url     : https://prove2.me/submissions/3bd640b3-d832-4ad7-b33a-6ccf6af75390

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
    T.toRoot (w ++ [a]) = T.toRoot w ∘ T.branch w a := by
  simp [toRoot, List.reverseRecOn]
