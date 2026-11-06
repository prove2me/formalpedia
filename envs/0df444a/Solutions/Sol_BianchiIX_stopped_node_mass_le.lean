-- Prove2me | solution 1 for BianchiIX.stopped_node_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:15:15.863846+00:00
-- url     : https://prove2.me/submissions/4cff1a24-1e0e-49c0-9b83-41a0ea6503bc

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Theorems.Thm_BianchiIX_gaussPrefix_image_measure_le
import Theorems.Thm_BianchiIX_gaussPrefix_small_set_image_le
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
open Set MeasureTheory
open scoped ENNReal


theorem solution (a : ℕ → ℕ+) (n : ℕ) {H : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} {ell : ℝ≥0∞} (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ x ∈ A, DifferentiableAt ℝ H x) (hinj : InjOn H A) (hsize : volume A ≤ ell)
    (hbound : ∀ x ∈ A, |deriv H x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (H '' A) ≤ (2 * ENNReal.ofReal (Real.exp L) * ell) *
      volume (gaussCylinder (digitPrefix a n)) := by
  have htransport := gaussPrefix_image_measure_le a n hA (fun x hx => (hAsub hx).1.le) hH hinj hbound
  have hsmall := gaussPrefix_small_set_image_le a n hA hAsub
  calc
    volume (H '' A) ≤ ENNReal.ofReal (Real.exp L) *
        (2 * volume (gaussCylinder (digitPrefix a n)) * volume A) :=
      htransport.trans (mul_le_mul le_rfl hsmall (by positivity) (by positivity))
    _ ≤ ENNReal.ofReal (Real.exp L) *
        (2 * volume (gaussCylinder (digitPrefix a n)) * ell) := by gcongr
    _ = _ := by ring
