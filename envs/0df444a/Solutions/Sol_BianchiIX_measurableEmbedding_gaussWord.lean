-- Prove2me | solution 1 for BianchiIX.measurableEmbedding_gaussWord
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:56:10.393197+00:00
-- url     : https://prove2.me/submissions/c6a51eaa-2c76-4428-ab46-11638551b99d

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
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
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

private theorem BianchiIX.measurableEmbedding_gaussInv (a : ℝ) : MeasurableEmbedding (gaussInv a) := by
  have h : MeasurableEmbedding (fun x : ℝ => (a + x)⁻¹) :=
    (MeasurableEquiv.inv ℝ).measurableEmbedding.comp
      (MeasurableEquiv.addLeft a).measurableEmbedding
  change MeasurableEmbedding (fun x : ℝ => 1 / (a + x))
  simpa only [one_div] using h

theorem solution (w : List ℕ) : MeasurableEmbedding (gaussWord w) := by
  induction w with
  | nil => exact MeasurableEmbedding.id
  | cons a w ih => exact (measurableEmbedding_gaussInv a).comp ih
