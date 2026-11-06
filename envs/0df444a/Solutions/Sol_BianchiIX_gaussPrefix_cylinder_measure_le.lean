-- Prove2me | solution 1 for BianchiIX.gaussPrefix_cylinder_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:28:24.612575+00:00
-- url     : https://prove2.me/submissions/799114f7-6ef5-4dc4-a143-b114c5da54cf

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_gaussPrefix_image_measure_le
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

open BianchiIX
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal


theorem solution (a : ℕ → ℕ+) (n : ℕ) {F : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ x ∈ A, DifferentiableAt ℝ F x) (hinj : InjOn F A)
    (hbound : ∀ x ∈ A, |deriv F x| ≤
      Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (F '' A) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussCylinder (digitPrefix a n)) := by
  apply (gaussPrefix_image_measure_le a n hA (fun x hx => (hAsub hx).1.le) hF hinj hbound).trans
  exact mul_le_mul le_rfl (measure_mono (image_mono hAsub)) (by positivity) (by positivity)
