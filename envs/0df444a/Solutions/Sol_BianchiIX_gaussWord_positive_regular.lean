-- Prove2me | solution 1 for BianchiIX.gaussWord_positive_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:52:47.707037+00:00
-- url     : https://prove2.me/submissions/7e7c5f3d-f86f-4495-914d-3f5ea7ff271e

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_abs_deriv_gaussWord_prefix
import Theorems.Thm_BianchiIX_digitPrefix_extendPositiveWord
import Theorems.Thm_BianchiIX_gaussDenoms_bounds
import Theorems.Thm_BianchiIX_hasDerivAt_gaussWord_prefix
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

section
open BianchiIX
noncomputable section
open Set Finset

private theorem BianchiIX.gaussDenom_pos (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < gaussDenom a n x := by
  have h := gaussDenoms_bounds a n
  dsimp [gaussDenom]
  nlinarith [mul_nonneg h.2.1 hx]

end
end

section
open BianchiIX
noncomputable section
open Set Finset

private theorem BianchiIX.deriv_gaussWord_prefix_ne_zero (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    deriv (gaussWord (digitPrefix a n)) x ≠ 0 := by
  have h : 0 < |deriv (gaussWord (digitPrefix a n)) x| := by
    rw [abs_deriv_gaussWord_prefix a n hx]
    have hpos := gaussDenom_pos a n hx
    positivity
  exact (abs_pos.mp h)

end
end

open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX


theorem solution (w : List ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    DifferentiableAt ℝ (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x ∧
      deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x ≠ 0 := by
  have hd := hasDerivAt_gaussWord_prefix (extendPositiveWord w) w.length hx
  have hn := deriv_gaussWord_prefix_ne_zero (extendPositiveWord w) w.length hx
  simp only [digitPrefix_extendPositiveWord] at hd hn
  exact ⟨hd.differentiableAt, hn⟩
