-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.phase_mem_unit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:37:35.137828+00:00
-- url     : https://prove2.me/submissions/69e4fca5-0e15-469f-8836-c3a19ce650ac

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_terminal_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_phase_mem_terminal
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
open BianchiIX.InverseBranchTree.BranchEstimates
variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
include E


theorem solution (x : T.survivors) (n : ℕ) : T.phase x n ∈ Icc (0 : ℝ) 1 :=
  ⟨(E.terminal_subset (T.word x n) (T.phase_mem_terminal x n)).1.le,
    (E.terminal_subset (T.word x n) (T.phase_mem_terminal x n)).2.le⟩
