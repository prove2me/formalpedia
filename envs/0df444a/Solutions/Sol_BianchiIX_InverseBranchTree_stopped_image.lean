-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.stopped_image
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:12:11.039723+00:00
-- url     : https://prove2.me/submissions/d4e3721c-37ed-4f68-b522-8396e3ea234e

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_injective
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


theorem solution (w : List ℕ+) :
    T.toRoot w '' T.stoppedDomain w = T.cell w \ ⋃ a, T.cell (w ++ [a]) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hn⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro hc
    obtain ⟨a, ha⟩ := mem_iUnion.mp hc
    rw [cell_append] at ha
    obtain ⟨z, ⟨hz, ha⟩, heq⟩ := ha
    have hzy := T.toRoot_injective w hz hy heq
    exact hn (mem_iUnion.mpr ⟨a, hzy ▸ ha⟩)
  · rintro ⟨⟨y, hy, rfl⟩, hn⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    rintro hc
    obtain ⟨a, ha⟩ := mem_iUnion.mp hc
    apply hn
    refine mem_iUnion.mpr ⟨a, ?_⟩
    rw [cell_append]
    exact ⟨y, ⟨hy, ha⟩, rfl⟩
