-- Prove2me | solution 1 for BianchiIX.measurableSet_gaussCylinder
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:57:47.294421+00:00
-- url     : https://prove2.me/submissions/f4287d90-a501-4d90-9bd1-2b6a224a2dff

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_measurableEmbedding_gaussWord
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


theorem solution (w : List ℕ) : MeasurableSet (gaussCylinder w) :=
  (measurableEmbedding_gaussWord w).measurableSet_image.mpr measurableSet_Ioo
