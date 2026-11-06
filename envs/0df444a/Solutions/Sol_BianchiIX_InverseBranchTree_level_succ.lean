-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.level_succ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:06:57.629148+00:00
-- url     : https://prove2.me/submissions/fb09bcfa-52d0-4300-87aa-5d52cd0c7414

import Definitions.Def_BianchiIX_Statistics_BranchTree
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


theorem solution (n : ℕ) :
    T.level (n + 1) = ⋃ w : {w : List ℕ+ // w.length = n}, ⋃ a, T.cell (w.val ++ [a]) := by
  ext x
  simp only [mem_level, mem_iUnion, Subtype.exists]
  constructor
  · rintro ⟨w, hw, hx⟩
    induction w using List.reverseRecOn with
    | nil => simp at hw
    | append_singleton w a _ => exact ⟨w, by simpa using hw, a, hx⟩
  · rintro ⟨w, hw, a, hx⟩
    exact ⟨w ++ [a], by simp [hw], hx⟩
