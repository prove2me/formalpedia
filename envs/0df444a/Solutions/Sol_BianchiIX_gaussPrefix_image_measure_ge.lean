-- Prove2me | solution 1 for BianchiIX.gaussPrefix_image_measure_ge
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:44:06.144722+00:00
-- url     : https://prove2.me/submissions/7c7fd5f1-0893-4e26-9869-85ee0287de46

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic

open Set Filter MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution (a : ℕ → ℕ+) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ≥0∞) * volume (gaussCylinder (digitPrefix a n)) * volume A ≤
      volume (gaussWord (digitPrefix a n) '' A) := by
  rw [volume_image_eq_lintegral_abs_deriv hA
    (fun x hx => (hasDerivAt_gaussWord_prefix a n (hsub hx).1.le).differentiableAt.hasDerivAt)
    (measurableEmbedding_gaussWord _).injective.injOn, volume_gaussCylinder_prefix]
  calc
    _ = ∫⁻ _ in A, ENNReal.ofReal ((1 / 2) * gaussPrefixLength a n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ ≤ _ := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hA
      intro x hx
      exact ENNReal.ofReal_le_ofReal (gaussPrefix_density_bounds a n
        ⟨(hsub hx).1.le, (hsub hx).2.le⟩).1
