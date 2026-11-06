-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.cell_unique
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:14:39.463751+00:00
-- url     : https://prove2.me/submissions/6c5780e1-ae58-47d2-9d1a-da8324943cc9

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_child_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_siblings_disjoint
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


theorem solution {v w : List ℕ+} (hlen : v.length = w.length)
    {x : ℝ} (hv : x ∈ T.cell v) (hw : x ∈ T.cell w) : v = w := by
  induction v using List.reverseRecOn generalizing w with
  | nil =>
    have : w = [] := List.length_eq_zero_iff.mp hlen.symm
    exact this.symm
  | append_singleton v a ih =>
    induction w using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton w b _ =>
      have hvw : v = w := ih (by simpa using hlen)
        (T.cell_child_subset v a hv) (T.cell_child_subset w b hw)
      subst w
      have hab : a = b := by
        by_contra h
        exact Set.disjoint_left.mp (T.cell_siblings_disjoint v h) hv hw
      exact congrArg (fun c => v ++ [c]) hab
