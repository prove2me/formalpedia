-- Prove2me | solution 1 for BianchiIX.timeAverage_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:36:26.755395+00:00
-- url     : https://prove2.me/submissions/8f85feee-9f34-474c-8286-801adcb4b6d3

import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
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
open InverseBranchTree.BranchEstimates


theorem solution {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℝ) (N : ℕ) :
    timeAverage (fun j => ∑ i ∈ s, u i j) N = ∑ i ∈ s, timeAverage (u i) N := by
  unfold timeAverage
  rw [Finset.sum_comm, Finset.mul_sum]
