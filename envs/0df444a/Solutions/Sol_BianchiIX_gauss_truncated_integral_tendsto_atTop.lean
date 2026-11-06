-- Prove2me | solution 1 for BianchiIX.gauss_truncated_integral_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:39:24.946471+00:00
-- url     : https://prove2.me/submissions/ae99313f-b78d-49d7-ba9e-88817dfe4b18

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
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


theorem solution :
    Tendsto (fun R : ℕ => Real.log ((R : ℝ) + 1) / Real.log 2) atTop atTop := by
  apply Filter.Tendsto.atTop_div_const log_two_pos
  exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
