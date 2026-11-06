-- Prove2me | solution 1 for BianchiIX.gauss_digit_tail_frequency
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:49:08.819473+00:00
-- url     : https://prove2.me/submissions/a1d17399-7552-433b-964e-c5a346f0d2b7

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_gaussMap_iterate_code
import Theorems.Thm_BianchiIX_gaussTailObservable_code
import Theorems.Thm_BianchiIX_gauss_tail_average_integral
import Theorems.Thm_BianchiIX_integral_gaussTailObservable
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


theorem solution (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (k : ℕ+) :
    Tendsto (timeAverage (fun j => if (k : ℕ) ≤ a j then 1 else 0)) atTop
      (𝓝 (Real.log (1 + 1 / (k : ℝ)) / Real.log 2)) := by
  have h := gauss_tail_average_integral a ha k
  have heq : (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a))) =
      (fun j => if (k : ℕ) ≤ a j then (1 : ℝ) else 0) := by
    funext j
    rw [gaussMap_iterate_code, gaussTailObservable_code]
    rfl
  rwa [heq, integral_gaussTailObservable] at h
