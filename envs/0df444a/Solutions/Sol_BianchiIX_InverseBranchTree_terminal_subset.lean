-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.terminal_subset
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:44:43.00665+00:00
-- url     : https://prove2.me/submissions/93550b83-9261-4bd6-a7b0-c4542f0a7f93

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
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
open scoped NNReal ENNReal
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


theorem solution {S : Set ℝ} (hroot : T.root ⊆ S)
    (hdom : ∀ w a, T.domain w a ⊆ S) (w : List ℕ+) : T.terminal w ⊆ S := by
  induction w using List.reverseRecOn with
  | nil => simpa using hroot
  | append_singleton w a _ =>
    rw [terminal_append]
    exact inter_subset_left.trans (hdom w a)
