-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.digits_measurable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:44:08.425661+00:00
-- url     : https://prove2.me/submissions/84f01d1d-bfa6-4d9c-a26c-d2180420718e

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_measurable
import Theorems.Thm_BianchiIX_InverseBranchTree_digit_fiber
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


theorem solution : Measurable T.digits := by
  apply measurable_pi_lambda
  intro n
  apply measurable_to_countable'
  intro a
  change MeasurableSet {x : T.survivors | T.digits x n = a}
  rw [T.digit_fiber]
  exact MeasurableSet.iUnion (fun w => (T.cell_measurable (w.val ++ [a])).preimage measurable_subtype_coe)
