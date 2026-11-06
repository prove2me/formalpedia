-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.code_volume_map_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:49:21.341898+00:00
-- url     : https://prove2.me/submissions/4238dbcc-4916-47f3-ab37-ec940db76e4f

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_volume_le
import Theorems.Thm_BianchiIX_InverseBranchTree_code_map_le_of_cell_bounds
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


theorem solution (L : ℝ)
    (hK : ∀ w, T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ w, ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hbound : ∀ w, ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ≤
      Real.toNNReal (Real.exp L) • volume := by
  apply T.code_map_le_of_cell_bounds
  intro w _
  exact T.cell_volume_le w (hK w) (hF w) (hbound w)
