-- Prove2me | solution 1 for BianchiIX.gaussPrefix_image_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:27:16.792956+00:00
-- url     : https://prove2.me/submissions/4f21267d-4082-440a-9cb3-8b131416bddc

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Theorems.Thm_BianchiIX_hasDerivAt_gaussWord_prefix
import Theorems.Thm_BianchiIX_measurableEmbedding_gaussWord
import Theorems.Thm_BianchiIX_volume_image_le_mul_of_deriv_le
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

open BianchiIX
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal


theorem solution (a : ℕ → ℕ+) (n : ℕ) {F : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} (hA : MeasurableSet A) (hApos : ∀ x ∈ A, 0 ≤ x)
    (hF : ∀ x ∈ A, DifferentiableAt ℝ F x) (hinj : InjOn F A)
    (hbound : ∀ x ∈ A, |deriv F x| ≤
      Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (F '' A) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussWord (digitPrefix a n) '' A) := by
  apply volume_image_le_mul_of_deriv_le hA (fun x hx => (hF x hx).hasDerivAt)
    (fun x hx => (hasDerivAt_gaussWord_prefix a n (hApos x hx)).differentiableAt.hasDerivAt)
    hinj (measurableEmbedding_gaussWord _).injective.injOn (Real.exp_pos L).le hbound
