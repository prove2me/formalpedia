-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.cell_measurable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:08:43.494269+00:00
-- url     : https://prove2.me/submissions/3ee1d244-f6f8-4226-b73a-aaab655f79ac

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_open
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_continuous
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_injective
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


theorem solution (w : List ℕ+) : MeasurableSet (T.cell w) :=
  (T.terminal_open w).measurableSet.image_of_continuousOn_injOn
    (T.toRoot_continuous w) (T.toRoot_injective w)
