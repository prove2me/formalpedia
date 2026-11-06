-- Prove2me | solution 1 for BianchiIX.gaussPrefix_small_set_image_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:43:37.816199+00:00
-- url     : https://prove2.me/submissions/baeb7cde-bb35-44ce-a078-0133a30a4008

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussDensity
import Theorems.Thm_BianchiIX_gaussPrefix_density_bounds
import Theorems.Thm_BianchiIX_hasDerivAt_gaussWord_prefix
import Theorems.Thm_BianchiIX_measurableEmbedding_gaussWord
import Theorems.Thm_BianchiIX_volume_gaussCylinder_prefix
import Theorems.Thm_BianchiIX_volume_image_eq_lintegral_abs_deriv
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
open Set MeasureTheory
open scoped ENNReal


theorem solution (a : ℕ → ℕ+) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1) :
    volume (gaussWord (digitPrefix a n) '' A) ≤
      2 * volume (gaussCylinder (digitPrefix a n)) * volume A := by
  rw [volume_image_eq_lintegral_abs_deriv hA
    (fun x hx => (hasDerivAt_gaussWord_prefix a n (hAsub hx).1.le).differentiableAt.hasDerivAt)
    (measurableEmbedding_gaussWord _).injective.injOn, volume_gaussCylinder_prefix]
  calc
    (∫⁻ x in A, ENNReal.ofReal |deriv (gaussWord (digitPrefix a n)) x|) ≤
        ∫⁻ _ in A, ENNReal.ofReal (2 * gaussPrefixLength a n) := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hA
      intro x hx
      exact ENNReal.ofReal_le_ofReal (gaussPrefix_density_bounds a n
        ⟨(hAsub hx).1.le, (hAsub hx).2.le⟩).2
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
