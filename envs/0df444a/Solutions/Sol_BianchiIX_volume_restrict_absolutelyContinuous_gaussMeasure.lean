-- Prove2me | solution 1 for BianchiIX.volume_restrict_absolutelyContinuous_gaussMeasure
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:22:39.011813+00:00
-- url     : https://prove2.me/submissions/abe3e307-1ec7-44d0-95a3-c3c558cbb4e3

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

private theorem BianchiIX.measurable_gaussWeight : Measurable gaussWeight :=
  measurable_const.div (measurable_const.mul (measurable_const.add measurable_id))

theorem solution :
    volume.restrict (Ioo (0 : ℝ) 1) ≪ gaussMeasure := by
  apply withDensity_absolutelyContinuous' measurable_gaussWeight.ennreal_ofReal.aemeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro x hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (gaussWeight_pos hx.1.le))
