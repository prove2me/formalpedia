-- Prove2me | solution 1 for BianchiIX.gauss_inverse_images_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:40:35.879775+00:00
-- url     : https://prove2.me/submissions/4d5a9a0c-d314-45d9-b54c-4e7885c45270

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

open Set MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution {A : Set ℝ} (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    Pairwise (fun i j : ℕ => Disjoint
      (gaussInv ((i : ℝ) + 1) '' A) (gaussInv ((j : ℝ) + 1) '' A)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy : x = y := by
    have h := congrArg gaussMap (hxz.trans hyz.symm)
    simpa only [gaussMap_inverse (hsub hx), gaussMap_inverse (hsub hy)] using h
  subst y
  have heq := congrArg (fun t : ℝ => 1 / t) (hxz.trans hyz.symm)
  simp only [gaussInv, one_div_one_div] at heq
  have hcast : (i : ℝ) = j := by linarith
  exact hij (by exact_mod_cast hcast)
