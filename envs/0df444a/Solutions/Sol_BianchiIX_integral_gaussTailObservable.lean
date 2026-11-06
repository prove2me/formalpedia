-- Prove2me | solution 1 for BianchiIX.integral_gaussTailObservable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:42:48.970111+00:00
-- url     : https://prove2.me/submissions/6da38f36-6fd2-4719-b1f6-d888d9f16ac3

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_gaussMeasure_tail_interval
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
    (∫ x, gaussTailObservable k x ∂gaussMeasure) = Real.log (1 + 1 / (k : ℝ)) / Real.log 2 := by
  have hi : (∫ x, gaussTailObservable k x ∂gaussMeasure) =
      (gaussMeasure (Ioo (0 : ℝ) (1 / (k : ℝ)))).toReal := integral_indicator_one measurableSet_Ioo
  rw [hi, gaussMeasure_tail_interval, ENNReal.toReal_ofReal]
  exact div_nonneg (Real.log_nonneg (le_add_of_nonneg_right (by positivity))) log_two_pos.le
