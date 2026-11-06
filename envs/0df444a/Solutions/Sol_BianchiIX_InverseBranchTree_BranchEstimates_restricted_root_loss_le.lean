-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.restricted_root_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:48:13.560766+00:00
-- url     : https://prove2.me/submissions/8775e004-d76f-4596-975c-2573e39964b1

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_terminal_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_toRoot_regular
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_uniform_deriv_bound
import Theorems.Thm_BianchiIX_InverseBranchTree_restricted_root_loss_le
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


theorem solution (I : Set ℝ) (ell : ℕ → ℝ≥0∞) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length) :
    volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤
      min (volume I) (2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m) :=
  T.restricted_root_loss_le I ell L E.terminal_subset
    (fun w _ hx => (E.toRoot_regular w hx).1) hsize
    (fun w _ hx => E.uniform_deriv_bound hbudget w hx)
