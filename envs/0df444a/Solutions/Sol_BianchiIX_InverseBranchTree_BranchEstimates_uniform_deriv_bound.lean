-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.uniform_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:43:16.043312+00:00
-- url     : https://prove2.me/submissions/6b5fc684-3123-4f14-874e-5d2ac4d07f59

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_deriv_bound
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
open BianchiIX.InverseBranchTree.BranchEstimates
variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
include E


theorem solution {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (w : List ℕ+) {x : ℝ} (hx : x ∈ T.terminal w) :
    |deriv (T.toRoot w) x| ≤ Real.exp L *
      |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x| :=
  (E.deriv_bound w hx).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbudget w.length)) (abs_nonneg _))
