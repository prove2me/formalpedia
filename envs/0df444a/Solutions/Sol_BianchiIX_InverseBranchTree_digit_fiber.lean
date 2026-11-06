-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.digit_fiber
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:42:05.219201+00:00
-- url     : https://prove2.me/submissions/cac24411-7039-44b5-abab-dc949b573bb4

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Theorems.Thm_BianchiIX_InverseBranchTree_word_eq_iff
import Theorems.Thm_BianchiIX_InverseBranchTree_word_succ
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


theorem solution (n : ℕ) (a : ℕ+) :
    {x : T.survivors | T.digits x n = a} =
      ⋃ w : {w : List ℕ+ // w.length = n},
        (Subtype.val : T.survivors → ℝ) ⁻¹' T.cell (w.val ++ [a]) := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
  constructor
  · intro h
    refine ⟨⟨T.word x n, T.word_length x n⟩, ?_⟩
    have hx := T.mem_word_cell x (n + 1)
    simpa only [T.word_succ, h] using hx
  · rintro ⟨⟨w, hw⟩, hx⟩
    have heq := (T.word_eq_iff x (by simp [hw] : (w ++ [a]).length = n + 1)).mpr hx
    rw [T.word_succ] at heq
    exact List.singleton_inj.mp (List.append_inj_right heq ((T.word_length x n).trans hw.symm))
