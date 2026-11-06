-- Prove2me | solution 1 for BianchiIX.ae_gaussMeasure_irrational
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:23:45.874029+00:00
-- url     : https://prove2.me/submissions/b507061a-e485-4d82-9749-ab172a13b26c

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
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

open Set MeasureTheory
open scoped ENNReal
open BianchiIX
noncomputable section


theorem solution : ∀ᵐ x ∂gaussMeasure, Irrational x := by
  rw [ae_iff]
  have heq : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
    ext x
    simp [Irrational]
  rw [heq]
  exact (countable_range ((↑) : ℚ → ℝ)).measure_zero gaussMeasure
