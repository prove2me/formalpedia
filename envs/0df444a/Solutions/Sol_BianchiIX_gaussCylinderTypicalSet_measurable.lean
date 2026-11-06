-- Prove2me | solution 1 for BianchiIX.gaussCylinderTypicalSet_measurable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:37:30.989093+00:00
-- url     : https://prove2.me/submissions/467cd3a4-9ec1-467b-9dff-a846bb1a8ea7

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_commonTypicalSet_measurable
import Theorems.Thm_BianchiIX_measurable_gaussCylinderObservable
import Theorems.Thm_BianchiIX_measurable_gaussMap
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section
open InverseBranchTree.BranchEstimates


theorem solution : MeasurableSet gaussCylinderTypicalSet :=
  commonTypicalSet_measurable _ measurable_gaussMap measurable_gaussCylinderObservable
