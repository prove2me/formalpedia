-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.cell_siblings_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:10:29.460709+00:00
-- url     : https://prove2.me/submissions/d4e7e43b-39ca-4d28-ab1c-e361e48d390f

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
    Pairwise (fun a b => Disjoint (T.cell (w ++ [a])) (T.cell (w ++ [b]))) := by
  intro a b hab
  rw [T.cell_append, T.cell_append, Set.disjoint_left]
  rintro x ⟨u, ⟨hu, ha⟩, hux⟩ ⟨v, ⟨hv, hb⟩, hvx⟩
  have huv := T.toRoot_injective w hu hv (hux.trans hvx.symm)
  exact Set.disjoint_left.mp (T.branch_disjoint w hab) ha (huv ▸ hb)
