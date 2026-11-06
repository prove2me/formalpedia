-- Prove2me | solution 1 for BianchiIX.gauss_tail_average_integral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:47:55.430673+00:00
-- url     : https://prove2.me/submissions/2b337788-d10d-4730-961b-d309074969a3

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_gaussCylinder_average_of_typical
import Theorems.Thm_BianchiIX_gaussMap_iterate_code
import Theorems.Thm_BianchiIX_gaussTailObservable_one_code
import Theorems.Thm_BianchiIX_gaussTailObservable_succ_code
import Theorems.Thm_BianchiIX_integral_gaussTailObservable
import Theorems.Thm_BianchiIX_integral_gaussTailObservable_succ
import Theorems.Thm_BianchiIX_timeAverage_sub
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
    Tendsto (timeAverage (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a)))) atTop
      (𝓝 (∫ x, gaussTailObservable k x ∂gaussMeasure)) := by
  induction k using PNat.recOn with
  | one =>
    have heq : (fun j => gaussTailObservable 1 (gaussMap^[j] (gaussCode a))) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext j
      rw [gaussMap_iterate_code, gaussTailObservable_one_code]
    rw [heq, integral_gaussTailObservable]
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    unfold timeAverage
    convert! hc.cesaro using 1
    norm_num [log_two_pos.ne']
  | succ k ih =>
    have heq : (fun j => gaussTailObservable (k + 1) (gaussMap^[j] (gaussCode a))) =
        (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a)) -
          gaussCylinderObservable [(k : ℕ)] (gaussMap^[j] (gaussCode a))) := by
      funext j
      simp only [gaussMap_iterate_code, gaussTailObservable_succ_code]
    rw [heq, integral_gaussTailObservable_succ]
    have hc := gaussCylinder_average_of_typical ha [(k : ℕ)]
    change Tendsto (timeAverage (fun j => gaussCylinderObservable [(k : ℕ)]
      (gaussMap^[j] (gaussCode a)))) atTop _ at hc
    change Tendsto (fun N => timeAverage (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a)) -
      gaussCylinderObservable [(k : ℕ)] (gaussMap^[j] (gaussCode a))) N) atTop _
    simpa only [timeAverage_sub] using ih.sub hc
