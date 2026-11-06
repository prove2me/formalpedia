-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.code_map_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:52:50.214814+00:00
-- url     : https://prove2.me/submissions/7ae95e12-afe5-46f7-8635-7e7d94920c7a

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_terminal_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_toRoot_regular
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_uniform_deriv_bound
import Theorems.Thm_BianchiIX_InverseBranchTree_code_volume_map_le
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
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ≤
      Real.toNNReal (Real.exp L) • volume :=
  T.code_volume_map_le L E.terminal_subset (fun w _ hx => (E.toRoot_regular w hx).1)
    (fun w _ hx => E.uniform_deriv_bound hbudget w hx)
