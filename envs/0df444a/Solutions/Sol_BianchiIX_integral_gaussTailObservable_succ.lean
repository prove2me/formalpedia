-- Prove2me | solution 1 for BianchiIX.integral_gaussTailObservable_succ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:46:28.665615+00:00
-- url     : https://prove2.me/submissions/75e08856-e9e6-493f-821c-30ae00124660

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_gaussTailObservable_succ_ae
import Theorems.Thm_BianchiIX_integrable_gaussCylinderObservable
import Theorems.Thm_BianchiIX_integrable_gaussTailObservable
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


theorem solution (k : ℕ+) :
    (∫ x, gaussTailObservable (k + 1) x ∂gaussMeasure) =
      (∫ x, gaussTailObservable k x ∂gaussMeasure) -
        (gaussMeasure (gaussCylinder [(k : ℕ)])).toReal := by
  rw [integral_congr_ae (gaussTailObservable_succ_ae k),
    integral_sub (integrable_gaussTailObservable k) (integrable_gaussCylinderObservable _),
    integral_gaussCylinderObservable]
