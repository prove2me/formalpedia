-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.mem_level
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:03:23.232859+00:00
-- url     : https://prove2.me/submissions/b45055ed-a43e-4741-b604-202be99d7ec8

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


theorem solution {n : ℕ} {x : ℝ} :
    x ∈ T.level n ↔ ∃ w : List ℕ+, w.length = n ∧ x ∈ T.cell w := by
  simp [level]
