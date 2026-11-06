-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.cell_volume_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:56:34.665258+00:00
-- url     : https://prove2.me/submissions/d9b33911-13be-4122-955a-3838049f4817

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_open
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_injective
import Theorems.Thm_BianchiIX_digitPrefix_extendPositiveWord
import Theorems.Thm_BianchiIX_gaussPrefix_cylinder_measure_le
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


theorem solution (w : List ℕ+) {L : ℝ}
    (hK : T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hbound : ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    volume (T.cell w) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussCylinder (w.map (fun a : ℕ+ => (a : ℕ)))) := by
  have h := gaussPrefix_cylinder_measure_le (extendPositiveWord w) w.length (L := L)
    (T.terminal_open w).measurableSet hK hF (T.toRoot_injective w)
  simpa only [cell, digitPrefix_extendPositiveWord] using h
    (by simpa only [digitPrefix_extendPositiveWord] using hbound)
