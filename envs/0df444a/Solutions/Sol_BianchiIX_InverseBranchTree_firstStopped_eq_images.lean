-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.firstStopped_eq_images
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:17:18.532186+00:00
-- url     : https://prove2.me/submissions/e3c6febf-5a8c-4ae1-b9ca-48124308a60b

import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_child_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_unique
import Theorems.Thm_BianchiIX_InverseBranchTree_level_succ
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_level
import Theorems.Thm_BianchiIX_InverseBranchTree_stopped_image
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


theorem solution (n : ℕ) :
    firstStoppedSet T.level n =
      ⋃ w : {w : List ℕ+ // w.length = n}, T.toRoot w.val '' T.stoppedDomain w.val := by
  ext x
  simp only [firstStoppedSet, mem_sdiff, mem_iUnion]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨w, hw, hx⟩ := T.mem_level.mp hx
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [stopped_image]
    refine ⟨hx, ?_⟩
    intro hc
    apply hn
    rw [level_succ]
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, hc⟩
  · rintro ⟨⟨w, hw⟩, hx⟩
    rw [stopped_image] at hx
    refine ⟨T.mem_level.mpr ⟨w, hw, hx.1⟩, ?_⟩
    intro hc
    rw [level_succ] at hc
    obtain ⟨v, hc⟩ := mem_iUnion.mp hc
    obtain ⟨a, ha⟩ := mem_iUnion.mp hc
    have hvw : v.val = w := T.cell_unique (v.property.trans hw.symm)
      (T.cell_child_subset v.val a ha) hx.1
    exact hx.2 (mem_iUnion.mpr ⟨a, hvw ▸ ha⟩)
