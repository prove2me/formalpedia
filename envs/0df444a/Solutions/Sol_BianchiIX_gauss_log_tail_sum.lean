-- Prove2me | solution 1 for BianchiIX.gauss_log_tail_sum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:24:29.529191+00:00
-- url     : https://prove2.me/submissions/c41720fc-4d44-4f7e-9a53-d046a8e73322

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
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
import Mathlib.MeasureTheory.Measure.WithDensity

open Set MeasureTheory
open scoped ENNReal
open BianchiIX
noncomputable section


theorem solution (R : ℕ) :
    (∑ j ∈ Finset.range R, Real.log (1 + 1 / ((j : ℝ) + 1)) / Real.log 2) =
      Real.log ((R : ℝ) + 1) / Real.log 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, ← add_div]
    have hr : (0 : ℝ) < (R : ℝ) + 1 := by positivity
    have hfrac : (1 : ℝ) + 1 / ((R : ℝ) + 1) = ((R : ℝ) + 2) / ((R : ℝ) + 1) := by
      field_simp
      ring
    rw [hfrac, Real.log_div (by positivity) hr.ne']
    congr 1
    push_cast
    rw [show (R : ℝ) + 1 + 1 = (R : ℝ) + 2 by ring]
    ring
