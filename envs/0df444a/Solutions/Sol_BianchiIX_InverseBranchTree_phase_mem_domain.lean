-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.phase_mem_domain
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:42:34.372783+00:00
-- url     : https://prove2.me/submissions/fd645904-1581-4014-b5df-28f73ef63968

import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Theorems.Thm_BianchiIX_InverseBranchTree_phase_mem_terminal
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
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
    T.phase x (n + 1) ∈ T.domain (T.word x n) (T.digits x n) := by
  have hx := T.phase_mem_terminal x (n + 1)
  rw [T.word_succ, T.terminal_append] at hx
  exact hx.1
