-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.phase_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:42:50.033909+00:00
-- url     : https://prove2.me/submissions/dddc84c9-eeb3-4937-9ff8-226949ebd7ec

import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Theorems.Thm_BianchiIX_InverseBranchTree_phase_mem_terminal
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_injective
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_phase
import Theorems.Thm_BianchiIX_InverseBranchTree_word_succ
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


open Set MeasureTheory Filter
open scoped Topology
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


theorem solution (x : T.survivors) (n : ℕ) :
    T.branch (T.word x n) (T.digits x n) (T.phase x (n + 1)) = T.phase x n := by
  have hx := T.phase_mem_terminal x (n + 1)
  rw [T.word_succ, T.terminal_append] at hx
  apply T.toRoot_injective (T.word x n) hx.2 (T.phase_mem_terminal x n)
  have hn := T.toRoot_phase x (n + 1)
  rw [T.word_succ, T.toRoot_append] at hn
  exact hn.trans (T.toRoot_phase x n).symm
