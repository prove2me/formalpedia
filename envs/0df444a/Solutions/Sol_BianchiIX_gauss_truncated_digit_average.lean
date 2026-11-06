-- Prove2me | solution 1 for BianchiIX.gauss_truncated_digit_average
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:50:20.799138+00:00
-- url     : https://prove2.me/submissions/008fb895-1b04-4622-b45e-ea589c940eec

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_gauss_digit_tail_frequency
import Theorems.Thm_BianchiIX_gauss_log_tail_sum
import Theorems.Thm_BianchiIX_nat_min_eq_sum_tails
import Theorems.Thm_BianchiIX_timeAverage_finsetSum
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
    (R : ℕ) :
    Tendsto (timeAverage (fun j => min (a j : ℝ) (R : ℝ))) atTop
      (𝓝 (Real.log ((R : ℝ) + 1) / Real.log 2)) := by
  have heq : (fun j => min (a j : ℝ) (R : ℝ)) =
      (fun j => ∑ i ∈ Finset.range R, if i + 1 ≤ (a j : ℕ) then (1 : ℝ) else 0) :=
    funext (fun j => nat_min_eq_sum_tails (a j) R)
  rw [heq, ← gauss_log_tail_sum R]
  change Tendsto (fun N => timeAverage (fun j => ∑ i ∈ Finset.range R,
    if i + 1 ≤ (a j : ℕ) then (1 : ℝ) else 0) N) atTop _
  simp_rw [timeAverage_finsetSum]
  apply tendsto_finsetSum
  intro i _
  simpa using gauss_digit_tail_frequency a ha ⟨i + 1, by omega⟩
