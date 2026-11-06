-- Prove2me | solution 1 for BianchiIX.gaussMeasure_absolutelyContinuous
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:22:12.035277+00:00
-- url     : https://prove2.me/submissions/f51f108b-53bc-4cf7-9258-3d794738aeb7

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


theorem solution : gaussMeasure ≪ volume.restrict (Ioo (0 : ℝ) 1) :=
  withDensity_absolutelyContinuous _ _
