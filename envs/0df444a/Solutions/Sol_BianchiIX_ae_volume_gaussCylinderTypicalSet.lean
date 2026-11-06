-- Prove2me | solution 1 for BianchiIX.ae_volume_gaussCylinderTypicalSet
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:52:28.31102+00:00
-- url     : https://prove2.me/submissions/be13d7c9-63a8-415d-a0e9-2a7ca37d0fdf

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_ae_gaussCylinderTypicalSet
import Theorems.Thm_BianchiIX_volume_restrict_absolutelyContinuous_gaussMeasure
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
    ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), x ∈ gaussCylinderTypicalSet :=
  volume_restrict_absolutelyContinuous_gaussMeasure.ae_le (ae_gaussCylinderTypicalSet hB)
