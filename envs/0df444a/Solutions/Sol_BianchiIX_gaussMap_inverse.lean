-- Prove2me | solution 1 for BianchiIX.gaussMap_inverse
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:38:18.398784+00:00
-- url     : https://prove2.me/submissions/bc4fc08d-b92f-40c5-b536-7268dfdc5b1f

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
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


theorem solution {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (j : ℕ) :
    gaussMap (gaussInv ((j : ℝ) + 1) x) = x := by
  unfold gaussMap gaussInv
  rw [one_div_one_div]
  have h := Int.fract_natCast_add (j + 1) x
  push_cast at h
  rw [h, Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩]
