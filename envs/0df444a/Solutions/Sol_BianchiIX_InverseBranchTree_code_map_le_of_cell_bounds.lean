-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.code_map_le_of_cell_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:46:42.152822+00:00
-- url     : https://prove2.me/submissions/504f243d-c9df-4a2f-b0fa-c7f5dd80a187

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Theorems.Thm_BianchiIX_InverseBranchTree_digits_measurable
import Theorems.Thm_BianchiIX_InverseBranchTree_prefix_fiber
import Theorems.Thm_BianchiIX_InverseBranchTree_survivors_measurable
import Theorems.Thm_BianchiIX_gaussCode_map_le_smul_of_cylinder_bounds
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
open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)

private theorem BianchiIX.InverseBranchTree.positive_word_lift (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    ∃ v : List ℕ+, v.map (fun a : ℕ+ => (a : ℕ)) = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons k w ih =>
    obtain ⟨v, hv⟩ := ih (fun j hj => hw j (List.mem_cons_of_mem k hj))
    refine ⟨⟨k, hw k (by simp)⟩ :: v, ?_⟩
    change k :: v.map (fun a : ℕ+ => (a : ℕ)) = k :: w
    rw [hv]

end

open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


theorem solution (μ ν : Measure ℝ) [ν.OuterRegular] (C : ℝ≥0)
    (hbound : ∀ w : List ℕ+, w ≠ [] →
      μ (T.cell w) ≤ (C : ℝ≥0∞) * ν (gaussCylinder (w.map (fun a : ℕ+ => (a : ℕ))))) :
    Measure.map T.code (μ.comap (Subtype.val : T.survivors → ℝ)) ≤ C • ν := by
  apply gaussCode_map_le_smul_of_cylinder_bounds _ ν T.digits T.digits_measurable C
  intro w hwne hw
  obtain ⟨v, hv⟩ := positive_word_lift w hw
  have hlen : v.length = w.length := by simpa using congrArg List.length hv
  have hvne : v ≠ [] := by
    intro hz
    subst v
    exact hwne (by simpa using hv.symm)
  rw [← hlen, ← hv, T.prefix_fiber]
  rw [comap_subtype_coe_apply T.survivors_measurable]
  exact (measure_mono (image_preimage_subset _ _)).trans (hbound v hvne)
