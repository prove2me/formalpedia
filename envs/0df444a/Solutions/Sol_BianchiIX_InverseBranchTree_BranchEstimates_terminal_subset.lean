-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.terminal_subset
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:55:13.966008+00:00
-- url     : https://prove2.me/submissions/9aa26a1f-80c1-44bc-824b-ed53f87bebc3

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_subset
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
open scoped NNReal ENNReal
open BianchiIX
open BianchiIX.InverseBranchTree
open BianchiIX.InverseBranchTree.BranchEstimates
variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
include E


theorem solution (w : List ℕ+) : T.terminal w ⊆ Ioo (0 : ℝ) 1 :=
  T.terminal_subset E.root_subset E.domain_subset w
