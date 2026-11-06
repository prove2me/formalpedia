-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.word_succ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:39:29.365845+00:00
-- url     : https://prove2.me/submissions/1fdddab0-2a60-4083-8859-565628feb162

import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_child_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_unique
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

private theorem BianchiIX.InverseBranchTree.exists_next_digit (x : T.survivors) (n : ℕ) :
    ∃ a : ℕ+, T.word x (n + 1) = T.word x n ++ [a] := by
  have hl := T.word_length x (n + 1)
  have hx := T.mem_word_cell x (n + 1)
  generalize T.word x (n + 1) = w at hl hx ⊢
  induction w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton w a _ =>
    have hw : w = T.word x n := T.cell_unique (by simpa [T.word_length] using hl)
      (T.cell_child_subset w a hx) (T.mem_word_cell x n)
    exact ⟨a, congrArg (fun v => v ++ [a]) hw⟩

end

open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX
open BianchiIX.InverseBranchTree
variable (T : InverseBranchTree)


theorem solution (x : T.survivors) (n : ℕ) :
    T.word x (n + 1) = T.word x n ++ [T.digits x n] :=
  (T.exists_next_digit x n).choose_spec
