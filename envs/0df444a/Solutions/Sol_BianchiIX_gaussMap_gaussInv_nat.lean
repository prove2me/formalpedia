-- Prove2me | solution 1 for BianchiIX.gaussMap_gaussInv_nat
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:40:50.983588+00:00
-- url     : https://prove2.me/submissions/d306c228-4236-4a1f-a93a-cd43d264acc0

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_gaussMap_inverse
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX


theorem solution {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {a : ℕ} (ha : 1 ≤ a) : gaussMap (gaussInv a x) = x := by
  have h := gaussMap_inverse hx (a - 1)
  have hc : ((a - 1 : ℕ) : ℝ) + 1 = a := by
    rw [Nat.cast_sub ha, Nat.cast_one, sub_add_cancel]
  rwa [hc] at h
