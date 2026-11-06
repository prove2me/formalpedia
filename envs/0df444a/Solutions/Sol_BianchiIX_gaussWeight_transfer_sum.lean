-- Prove2me | solution 1 for BianchiIX.gaussWeight_transfer_sum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:40:09.624538+00:00
-- url     : https://prove2.me/submissions/bd12495b-a578-4fc5-a43d-5ca6e3427331

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_gaussWeight_inverse_jacobian
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX


theorem solution {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      gaussWeight (gaussInv ((j : ℝ) + 1) x) * |deriv (gaussInv ((j : ℝ) + 1)) x|) =
      (1 / Real.log 2) * (1 / (1 + x) - 1 / ((N : ℝ) + 1 + x)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      gaussWeight_inverse_jacobian (by linarith [Nat.cast_nonneg (α := ℝ) N]) hx]
    push_cast
    ring
