-- Prove2me | solution 1 for BianchiIX.timeAverage_difference_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:24:27.630613+00:00
-- url     : https://prove2.me/submissions/e3e5b8de-2ea1-4078-bfb1-7ca0eb605873

import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor


open Set Filter
open scoped Topology
open BianchiIX


theorem solution {u v : ℕ → ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    Tendsto (fun n => timeAverage u n - timeAverage v n) atTop (𝓝 0) := by
  simpa only [timeAverage, Finset.sum_sub_distrib, mul_sub] using h.cesaro
