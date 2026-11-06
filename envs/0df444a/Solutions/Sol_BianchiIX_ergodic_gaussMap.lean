-- Prove2me | solution 1 for BianchiIX.ergodic_gaussMap
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:49:44.196182+00:00
-- url     : https://prove2.me/submissions/47c19536-2235-40ef-962b-f2b946c89e27

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_gaussMeasure_absolutelyContinuous
import Theorems.Thm_BianchiIX_invariant_set_volume_zero_or_compl_zero
import Theorems.Thm_BianchiIX_measurePreserving_gaussMap
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


theorem solution : Ergodic gaussMap gaussMeasure := by
  refine ⟨measurePreserving_gaussMap, ?_⟩
  constructor
  intro E hE hinv
  have h := invariant_set_volume_zero_or_compl_zero hE hinv
  have hν : gaussMeasure E = 0 ∨ gaussMeasure Eᶜ = 0 :=
    h.imp (fun h => gaussMeasure_absolutelyContinuous h)
      (fun h => gaussMeasure_absolutelyContinuous h)
  simpa [eventuallyConst_set'] using hν
