-- Prove2me | solution 1 for BianchiIX.gaussMass_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:20:29.46605+00:00
-- url     : https://prove2.me/submissions/ccc92f3f-b1eb-4f80-9961-a29584452343

import Definitions.Def_BianchiIX_Statistics_GaussPartition
import Theorems.Thm_BianchiIX_gaussWords_mass_sum
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section


theorem solution (n : ℕ) : HasSum (gaussMass n) 1 := by
  have hsum : (∑' w : GaussWords n, gaussMeasure (gaussCylinder w.val)) ≠ ⊤ := by
    rw [gaussWords_mass_sum]
    exact ENNReal.one_ne_top
  have h := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq (fun w : GaussWords n =>
      measure_ne_top gaussMeasure (gaussCylinder w.val)),
    gaussWords_mass_sum, ENNReal.toReal_one] at h
  exact h
