-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.root_sdiff_survivors
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:20:29.051784+00:00
-- url     : https://prove2.me/submissions/6aa5a287-8820-4875-872d-68e0b90ae4cb

import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_firstStopped_eq_images
import Theorems.Thm_BianchiIX_InverseBranchTree_level_antitone
import Theorems.Thm_BianchiIX_InverseBranchTree_level_zero
import Theorems.Thm_BianchiIX_root_sdiff_survivingSet
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
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


theorem solution :
    T.root \ survivingSet T.level =
      ⋃ n, ⋃ w : {w : List ℕ+ // w.length = n}, T.toRoot w.val '' T.stoppedDomain w.val := by
  rw [← T.level_zero, root_sdiff_survivingSet T.level T.level_antitone]
  simp_rw [T.firstStopped_eq_images]
