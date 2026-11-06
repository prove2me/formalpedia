-- Prove2me | solution 1 for BianchiIX.gaussMap_mem_unit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:41:05.757578+00:00
-- url     : https://prove2.me/submissions/e945d3be-f14e-4f31-a869-265a7663d1c8

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_gaussMap_irrational
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

open Set MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution {x : ℝ} (hx : Irrational x) : gaussMap x ∈ Ioo (0 : ℝ) 1 :=
  ⟨lt_of_le_of_ne (Int.fract_nonneg _) (gaussMap_irrational hx).ne_zero.symm,
    Int.fract_lt_one _⟩
