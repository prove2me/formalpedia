-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.cell_append
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:06:32.190891+00:00
-- url     : https://prove2.me/submissions/8c2798d5-cec2-442e-a145-0da4fa71d418

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_append
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


theorem solution (w : List ℕ+) (a : ℕ+) :
    T.cell (w ++ [a]) = T.toRoot w ''
      (T.terminal w ∩ T.branch w a '' T.domain w a) := by
  ext x
  simp only [cell, toRoot_append, terminal_append, mem_image, mem_inter_iff,
    mem_preimage, Function.comp_apply]
  constructor
  · rintro ⟨y, ⟨hy, hK⟩, rfl⟩
    exact ⟨T.branch w a y, ⟨hK, y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨hK, y, hy, rfl⟩, rfl⟩
    exact ⟨y, ⟨hy, hK⟩, rfl⟩
