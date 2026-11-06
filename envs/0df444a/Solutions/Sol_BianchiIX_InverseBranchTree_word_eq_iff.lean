-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.word_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:39:03.417638+00:00
-- url     : https://prove2.me/submissions/a504b42e-89a5-41e8-b8b3-524707357547

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_unique
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


theorem solution (x : T.survivors) {n : ℕ} {w : List ℕ+} (hw : w.length = n) :
    T.word x n = w ↔ x.val ∈ T.cell w := by
  constructor
  · intro h
    simpa only [h] using T.mem_word_cell x n
  · exact fun h => T.cell_unique ((T.word_length x n).trans hw.symm) (T.mem_word_cell x n) h
