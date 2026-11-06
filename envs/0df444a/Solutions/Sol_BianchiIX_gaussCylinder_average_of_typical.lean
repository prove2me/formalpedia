-- Prove2me | solution 1 for BianchiIX.gaussCylinder_average_of_typical
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:30:18.725917+00:00
-- url     : https://prove2.me/submissions/dbfc73c9-faed-47e9-b428-03d9598ae5a1

import Definitions.Def_BianchiIX_Statistics_GaussTypical
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


theorem solution {x : ℝ} (hx : x ∈ gaussCylinderTypicalSet) (w : List ℕ) :
    Tendsto (fun n => birkhoffAverage ℝ gaussMap (gaussCylinderObservable w) n x)
      atTop (𝓝 (gaussMeasure (gaussCylinder w)).toReal) := hx w
