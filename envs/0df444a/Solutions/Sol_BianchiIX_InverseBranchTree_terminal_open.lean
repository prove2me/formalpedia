-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.terminal_open
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:04:34.689714+00:00
-- url     : https://prove2.me/submissions/be2e0f58-a40d-48e7-b88e-22b5e33f3ca5

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_nil
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


theorem solution (w : List ℕ+) : IsOpen (T.terminal w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using T.root_open
  | append_singleton w a ih =>
    rw [terminal_append]
    exact (T.branch_continuous w a).isOpen_inter_preimage (T.domain_open w a) ih
