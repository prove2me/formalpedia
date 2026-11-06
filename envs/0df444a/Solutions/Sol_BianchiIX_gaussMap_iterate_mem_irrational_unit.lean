-- Prove2me | solution 1 for BianchiIX.gaussMap_iterate_mem_irrational_unit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:43:11.857113+00:00
-- url     : https://prove2.me/submissions/8f136640-af45-41eb-b773-5aa88e8d114d

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_gaussMap_irrational
import Theorems.Thm_BianchiIX_gaussMap_mem_unit
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


theorem solution {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hi : Irrational x) (n : ℕ) :
    gaussMap^[n] x ∈ Ioo (0 : ℝ) 1 ∧ Irrational (gaussMap^[n] x) := by
  induction n with
  | zero => exact ⟨hx, hi⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨gaussMap_mem_unit ih.2, gaussMap_irrational ih.2⟩
