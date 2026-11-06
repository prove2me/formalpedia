-- Prove2me | solution 1 for BianchiIX.gauss_digit_block_frequency
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:38:28.350183+00:00
-- url     : https://prove2.me/submissions/01c5cb43-5fa1-4845-9556-83f54a279cf7

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_gaussCylinderObservable_code
import Theorems.Thm_BianchiIX_gaussCylinder_average_of_typical
import Theorems.Thm_BianchiIX_gaussMap_iterate_code
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
open InverseBranchTree.BranchEstimates


theorem solution (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
      if digitPrefix (shiftDigits a j) w.length = w then (1 : ℝ) else 0)
      atTop (𝓝 (gaussMeasure (gaussCylinder w)).toReal) := by
  have h := gaussCylinder_average_of_typical ha w
  change Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
    gaussCylinderObservable w (gaussMap^[j] (gaussCode a))) atTop _ at h
  simpa only [gaussMap_iterate_code, gaussCylinderObservable_code _ w hw] using h
