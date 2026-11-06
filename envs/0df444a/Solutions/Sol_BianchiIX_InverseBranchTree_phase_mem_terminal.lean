-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.phase_mem_terminal
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:40:22.084499+00:00
-- url     : https://prove2.me/submissions/eb6467a7-cdf5-4e2e-bf2c-b6e3e0576859

import Definitions.Def_BianchiIX_Statistics_TreeOrbits
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

section
open Set MeasureTheory Filter
open scoped Topology
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.exists_phase (x : T.survivors) (n : ℕ) :
    ∃ t ∈ T.terminal (T.word x n), T.toRoot (T.word x n) t = x.val :=
  T.mem_word_cell x n

end

open Set MeasureTheory Filter
open scoped Topology
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


theorem solution (x : T.survivors) (n : ℕ) :
    T.phase x n ∈ T.terminal (T.word x n) := (T.exists_phase x n).choose_spec.1
