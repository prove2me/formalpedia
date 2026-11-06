-- Prove2me | solution 1 for BianchiIX.ae_gaussWords_cover
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:15:55.019826+00:00
-- url     : https://prove2.me/submissions/2c134029-c05d-4b8b-a053-17bd4d5c0c5b

import Definitions.Def_BianchiIX_Statistics_GaussPartition
import Theorems.Thm_BianchiIX_ae_gaussMeasure_irrational
import Theorems.Thm_BianchiIX_ae_gaussMeasure_mem_unit
import Theorems.Thm_BianchiIX_gaussWords_cover
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section


theorem solution (n : ℕ) :
    ∀ᵐ x ∂gaussMeasure, x ∈ ⋃ w : GaussWords n, gaussCylinder w.val := by
  filter_upwards [ae_gaussMeasure_mem_unit, ae_gaussMeasure_irrational] with x hx hi
  exact gaussWords_cover n hx hi
