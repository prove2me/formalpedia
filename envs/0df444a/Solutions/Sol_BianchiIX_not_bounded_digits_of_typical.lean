-- Prove2me | solution 1 for BianchiIX.not_bounded_digits_of_typical
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:46:01.981889+00:00
-- url     : https://prove2.me/submissions/a2d72485-5891-4379-a2d9-61148fed3d38

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussBoundedDigits
import Theorems.Thm_BianchiIX_gauss_digit_frequency
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

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal


/-- A cylinder-typical code cannot have a finite upper bound on all its digits. -/
theorem solution {a : ℕ → ℕ+}
    (ha : gaussCode a ∈ gaussCylinderTypicalSet) : ¬ ∃ N : ℕ, ∀ n, (a n : ℕ) ≤ N := by
  rintro ⟨N, hN⟩
  let k : ℕ+ := ⟨N + 1, by omega⟩
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  have hpos : 0 < Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2 :=
    div_pos (Real.log_pos ((one_lt_div (by positivity)).mpr (by nlinarith))) log_two_pos
  have hzero : (fun j => if (a j : ℕ) = (k : ℕ) then (1 : ℝ) else 0) = fun _ => 0 := by
    funext j
    have hne : (a j : ℕ) ≠ (k : ℕ) := by have := hN j; dsimp [k]; omega
    simp only [if_neg hne]
  have H := gauss_digit_frequency a ha k
  rw [hzero] at H
  have H0 : Tendsto (timeAverage (fun _ : ℕ => (0 : ℝ))) atTop (𝓝 0) := by
    change Tendsto (fun n => timeAverage (fun _ : ℕ => (0 : ℝ)) n) atTop (𝓝 0)
    simp only [timeAverage, Finset.sum_const_zero, mul_zero]
    exact tendsto_const_nhds
  exact (ne_of_gt hpos) (tendsto_nhds_unique H H0)
