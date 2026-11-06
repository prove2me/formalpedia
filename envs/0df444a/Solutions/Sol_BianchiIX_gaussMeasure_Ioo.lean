-- Prove2me | solution 1 for BianchiIX.gaussMeasure_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:21:46.377886+00:00
-- url     : https://prove2.me/submissions/88121cf9-44cf-4a3d-b3e0-ba745b032318

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

private theorem BianchiIX.gaussMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    gaussMeasure A = ∫⁻ x in A, ENNReal.ofReal (gaussWeight x) := by
  rw [gaussMeasure, withDensity_apply _ hA, Measure.restrict_restrict_of_subset hsub]

theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    gaussMeasure (Ioo a b) = ENNReal.ofReal ((Real.log (1 + b) - Real.log (1 + a)) / Real.log 2) := by
  rw [gaussMeasure_apply measurableSet_Ioo
    (fun _ hx => ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩), gaussWeight_lintegral_Ioo ha hab]
  congr 1
  simp only [gaussPrimitive, sub_div]
