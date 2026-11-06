-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.stoppedDomain_measurable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:07:51.139537+00:00
-- url     : https://prove2.me/submissions/90cc4628-9feb-4ff1-85b8-706ef5454ca4

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_open
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


theorem solution (w : List ℕ+) : MeasurableSet (T.stoppedDomain w) :=
  (T.terminal_open w).measurableSet.diff (MeasurableSet.iUnion (fun a =>
    (T.domain_open w a).measurableSet.image_of_continuousOn_injOn
      (T.branch_continuous w a) (T.branch_injective w a)))
