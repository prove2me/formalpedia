-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.digits_prefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:41:38.803168+00:00
-- url     : https://prove2.me/submissions/22dee2f8-220b-49a2-9ae5-6508b0b9f9eb

import Definitions.Def_BianchiIX_Statistics_TreeCoding
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


theorem solution (x : T.survivors) (n : ℕ) :
    digitPrefix (T.digits x) n = (T.word x n).map (fun a : ℕ+ => (a : ℕ)) := by
  induction n with
  | zero =>
    have hw : T.word x 0 = [] := List.length_eq_zero_iff.mp (T.word_length x 0)
    simp [digitPrefix, hw]
  | succ n ih =>
    rw [T.word_succ, List.map_append, List.map_singleton, ← ih]
    simp [digitPrefix, List.range_succ]
