-- Prove2me | solution 1 for BianchiIX.gaussMeasure_singleton_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:43:15.143474+00:00
-- url     : https://prove2.me/submissions/fc8e5f78-6c83-4fdd-964f-06687f2dc8f3

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_gaussCylinder_singleton
import Theorems.Thm_BianchiIX_gaussMeasure_digit_interval
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
    (gaussMeasure (gaussCylinder [(k : ℕ)])).toReal =
      Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  rw [gaussCylinder_singleton, gaussMeasure_digit_interval, ENNReal.toReal_ofReal]
  apply div_nonneg _ log_two_pos.le
  apply Real.log_nonneg
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith
