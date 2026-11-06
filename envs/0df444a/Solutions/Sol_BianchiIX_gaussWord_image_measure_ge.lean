-- Prove2me | solution 1 for BianchiIX.gaussWord_image_measure_ge
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:45:22.006238+00:00
-- url     : https://prove2.me/submissions/766e04ca-fea7-4496-98a8-acecf215b137

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_exists_digitPrefix
import Theorems.Thm_BianchiIX_gaussPrefix_image_measure_ge
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic

open Set Filter MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ≥0∞) * volume (gaussCylinder w) * volume A ≤ volume (gaussWord w '' A) := by
  obtain ⟨a, ha⟩ := exists_digitPrefix w hw
  simpa only [ha] using gaussPrefix_image_measure_ge a w.length hA hsub
