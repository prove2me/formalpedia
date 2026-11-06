-- Prove2me | solution 1 for BianchiIX.ae_gaussCylinderTypicalSet
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:41:08.979216+00:00
-- url     : https://prove2.me/submissions/f888f20e-aa81-40f9-bcd5-721afb345f7d

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_ae_mem_commonTypicalSet
import Theorems.Thm_BianchiIX_ergodic_gaussMap
import Theorems.Thm_BianchiIX_integrable_gaussCylinderObservable
import Theorems.Thm_BianchiIX_integral_gaussCylinderObservable
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


theorem solution (hB : Literature.BirkhoffErgodicInput ℝ) :
    ∀ᵐ x ∂gaussMeasure, x ∈ gaussCylinderTypicalSet := by
  apply ae_mem_commonTypicalSet
  intro w
  have h := hB gaussMeasure inferInstance gaussMap ergodic_gaussMap
    (gaussCylinderObservable w) (integrable_gaussCylinderObservable w)
  simpa only [integral_gaussCylinderObservable] using h
