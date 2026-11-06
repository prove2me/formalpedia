-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.prefix_fiber
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:43:41.742907+00:00
-- url     : https://prove2.me/submissions/53fb0b3d-ade1-4323-a8bf-7b81b057b60f

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Theorems.Thm_BianchiIX_InverseBranchTree_digits_prefix
import Theorems.Thm_BianchiIX_InverseBranchTree_word_eq_iff
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
variable (T : InverseBranchTree)


theorem solution (w : List ℕ+) :
    {x : T.survivors | digitPrefix (T.digits x) w.length = w.map (fun a : ℕ+ => (a : ℕ))} =
      (Subtype.val : T.survivors → ℝ) ⁻¹' T.cell w := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, T.digits_prefix]
  constructor
  · intro h
    apply (T.word_eq_iff x rfl).mp
    exact List.map_injective_iff.mpr Subtype.val_injective h
  · intro h
    rw [(T.word_eq_iff x rfl).mpr h]
