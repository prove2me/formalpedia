-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.phase_error_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:44:46.175097+00:00
-- url     : https://prove2.me/submissions/9126a69d-1e26-4d65-b5d7-71c5b85e6843

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Theorems.Thm_BianchiIX_InverseBranchTree_phase_mem_domain
import Theorems.Thm_BianchiIX_InverseBranchTree_phase_recurrence
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


theorem solution (x : T.survivors) (n : ℕ) :
    inverseError (fun k => (T.digits x k : ℕ)) (T.phase x) n ≤ d n := by
  have h := E.value_error (T.word x n) (T.digits x n) (T.phase x (n + 1)) (T.phase_mem_domain x n)
  simpa only [T.phase_recurrence, T.word_length, inverseError] using h
