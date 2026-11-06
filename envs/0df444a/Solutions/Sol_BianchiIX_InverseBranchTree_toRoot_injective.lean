-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.toRoot_injective
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:06:04.056535+00:00
-- url     : https://prove2.me/submissions/62c6eec9-64a9-44dc-90ea-9258aab791c9

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_nil
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_nil
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


theorem solution (w : List ℕ+) : InjOn (T.toRoot w) (T.terminal w) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rw [toRoot_append, terminal_append]
    intro x hx y hy hxy
    exact T.branch_injective w a hx.1 hy.1 (ih hx.2 hy.2 hxy)
