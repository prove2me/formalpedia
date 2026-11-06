-- Prove2me | solution 1 for BianchiIX.continuous_observable_difference
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:24:01.94831+00:00
-- url     : https://prove2.me/submissions/c076ab0e-b52a-402b-aebb-bd1cfa8ae460

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


theorem solution {x y : ℕ → ℝ} {f : ℝ → ℝ}
    {S : Set ℝ} (hS : IsCompact S) (hf : ContinuousOn f S)
    (hx : ∀ n, x n ∈ S) (hy : ∀ n, y n ∈ S)
    (hxy : Tendsto (fun n => x n - y n) atTop (𝓝 0)) :
    Tendsto (fun n => f (x n) - f (y n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [Metric.tendsto_nhds.mp hxy δ hδ] with n hn
  have hdist : dist (x n) (y n) < δ := by simpa only [Real.dist_eq, sub_zero] using hn
  simpa only [Real.dist_eq, sub_zero] using hclose (x n) (hx n) (y n) (hy n) hdist
