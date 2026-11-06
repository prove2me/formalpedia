-- Prove2me | solution 1 for BianchiIX.gauss_digit_frequency
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:44:24.767837+00:00
-- url     : https://prove2.me/submissions/a0cab68b-ff66-4954-b4b3-4d6d5eef2c88

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_gaussMeasure_singleton_cylinder
import Theorems.Thm_BianchiIX_gauss_digit_block_frequency
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


theorem solution (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet) (k : ℕ+) :
    Tendsto (timeAverage (fun j => if (a j : ℕ) = k then 1 else 0)) atTop
      (𝓝 (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2)) := by
  have h := gauss_digit_block_frequency a ha [(k : ℕ)] (by simpa using Nat.succ_le_of_lt k.pos)
  rw [gaussMeasure_singleton_cylinder] at h
  unfold timeAverage
  simpa [digitPrefix, shiftDigits] using h
