-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:40:03.316737+00:00
-- url     : https://prove2.me/submissions/a7eedbe1-370f-4a26-af36-2d44e02f0c05

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_log_distortion
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_terminal_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_toRoot_regular
import Theorems.Thm_BianchiIX_gaussWord_positive_regular
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


theorem solution (w : List ℕ+) {x : ℝ} (hx : x ∈ T.terminal w) :
    |deriv (T.toRoot w) x| ≤
      Real.exp (∑ j ∈ Finset.range w.length, (e j + if j = 0 then 0 else 2 * d j)) *
        |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x| := by
  have hb := E.log_distortion w hx
  have hp := E.toRoot_regular w hx
  have hg := gaussWord_positive_regular w (E.terminal_subset w hx).1.le
  have hratio : 0 < |deriv (T.toRoot w) x| /
      |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x| :=
    div_pos (abs_pos.mpr hp.2) (abs_pos.mpr hg.2)
  have he := Real.exp_le_exp.mpr ((le_abs_self _).trans hb)
  rw [Real.exp_log hratio] at he
  exact (div_le_iff₀ (abs_pos.mpr hg.2)).mp he
