-- Prove2me | solution 1 for BianchiIX.gaussMap_preimage_ae
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:42:46.475194+00:00
-- url     : https://prove2.me/submissions/c2bb541c-22c0-4a45-8674-45d23af0b1ae

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_ae_gaussMeasure_irrational
import Theorems.Thm_BianchiIX_ae_gaussMeasure_mem_unit
import Theorems.Thm_BianchiIX_exists_gauss_inverse
import Theorems.Thm_BianchiIX_gaussMap_inverse
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

open Set MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution (A : Set ℝ) :
    gaussMap ⁻¹' A =ᵐ[gaussMeasure]
      ⋃ j : ℕ, gaussInv ((j : ℝ) + 1) '' (A ∩ Ioo (0 : ℝ) 1) := by
  filter_upwards [ae_gaussMeasure_mem_unit, ae_gaussMeasure_irrational] with x hx hi
  apply propext
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_gauss_inverse hx
    exact mem_iUnion.mpr ⟨j, gaussMap x, ⟨h, gaussMap_mem_unit hi⟩, hj⟩
  · intro h
    rcases mem_iUnion.mp h with ⟨j, y, hy, rfl⟩
    change gaussMap (gaussInv ((j : ℝ) + 1) y) ∈ A
    rw [gaussMap_inverse hy.2]
    exact hy.1
