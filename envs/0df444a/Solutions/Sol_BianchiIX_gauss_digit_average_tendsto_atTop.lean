-- Prove2me | solution 1 for BianchiIX.gauss_digit_average_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:51:55.150122+00:00
-- url     : https://prove2.me/submissions/a1361ed5-261f-46cc-ae7f-5903d52da721

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_gauss_truncated_digit_average
import Theorems.Thm_BianchiIX_gauss_truncated_integral_tendsto_atTop
import Theorems.Thm_BianchiIX_timeAverage_tendsto_atTop_of_truncations
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
open scoped Topology
open BianchiIX
noncomputable section


theorem solution (a : ℕ → ℕ+)
    (ha : gaussCode a ∈ gaussCylinderTypicalSet) :
    Tendsto (timeAverage (fun j => (a j : ℝ))) atTop atTop :=
  timeAverage_tendsto_atTop_of_truncations (gauss_truncated_digit_average a ha)
    gauss_truncated_integral_tendsto_atTop
