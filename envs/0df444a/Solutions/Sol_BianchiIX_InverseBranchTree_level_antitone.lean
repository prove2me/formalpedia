-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.level_antitone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:14:23.868267+00:00
-- url     : https://prove2.me/submissions/3054707f-4724-46bb-93f8-aa1c829aa7b5

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_child_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_level_succ
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_level
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


theorem solution : Antitone T.level := by
  apply antitone_nat_of_succ_le
  intro n x hx
  rw [level_succ] at hx
  obtain ⟨w, hx⟩ := mem_iUnion.mp hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  exact T.mem_level.mpr ⟨w.val, w.property, T.cell_child_subset w.val a ha⟩
