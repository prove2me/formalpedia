-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.toRoot_continuous
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:05:27.67627+00:00
-- url     : https://prove2.me/submissions/c42ccf4d-5918-453d-ac92-13bf56027481

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


theorem solution (w : List ℕ+) : ContinuousOn (T.toRoot w) (T.terminal w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using (continuousOn_id : ContinuousOn (id : ℝ → ℝ) T.root)
  | append_singleton w a ih =>
    rw [toRoot_append, terminal_append]
    exact ih.comp ((T.branch_continuous w a).mono inter_subset_left) (fun _ hx => hx.2)
