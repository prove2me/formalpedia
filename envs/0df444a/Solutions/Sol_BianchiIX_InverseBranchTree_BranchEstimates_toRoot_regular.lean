-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.toRoot_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:46:23.312645+00:00
-- url     : https://prove2.me/submissions/82af9d0c-84a9-4611-a5ba-cb37be317717

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_nil
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
    DifferentiableAt ℝ (T.toRoot w) x ∧ deriv (T.toRoot w) x ≠ 0 := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp
  | append_singleton w a ih =>
    rw [T.terminal_append] at hx
    have hp := ih hx.2
    have ha := E.differentiable w a x hx.1
    rw [T.toRoot_append]
    refine ⟨hp.1.comp x ha, ?_⟩
    rw [deriv_comp x hp.1 ha]
    exact mul_ne_zero hp.2 (E.nonzero w a x hx.1)
