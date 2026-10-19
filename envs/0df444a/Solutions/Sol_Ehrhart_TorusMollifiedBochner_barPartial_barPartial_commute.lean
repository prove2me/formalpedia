-- Prove2me | solution 1 for Ehrhart.TorusMollifiedBochner.barPartial_barPartial_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/07caea1e-75bf-4d3f-b507-25c3eab7660c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_directional_commute
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_barPartialCoordinate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusMollifiedBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusDistributionBridge TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusMollifiedBochner
theorem _root_.solution
    {n : ℕ}
    {F : LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z : LogSpace n) (i j : Fin n) :
    barPartialCoordinate
      (fun w => barPartialCoordinate F w i) z j =
      barPartialCoordinate
        (fun w => barPartialCoordinate F w j) z i := by
  let ei₀ : LogSpace n := Pi.single i (1 : ℂ)
  let ei₁ : LogSpace n := Pi.single i Complex.I
  let ej₀ : LogSpace n := Pi.single j (1 : ℂ)
  let ej₁ : LogSpace n := Pi.single j Complex.I
  change
    ((fderiv ℝ
        (fun w => barPartialCoordinate F w i) z) ej₀ +
      Complex.I *
        (fderiv ℝ
          (fun w => barPartialCoordinate F w i) z) ej₁) / 2 =
      ((fderiv ℝ
          (fun w => barPartialCoordinate F w j) z) ei₀ +
        Complex.I *
          (fderiv ℝ
            (fun w => barPartialCoordinate F w j) z) ei₁) / 2
  rw [fderiv_barPartialCoordinate hF z ej₀ i,
    fderiv_barPartialCoordinate hF z ej₁ i,
    fderiv_barPartialCoordinate hF z ei₀ j,
    fderiv_barPartialCoordinate hF z ei₁ j]
  change
    (((fderiv ℝ (fun w => (fderiv ℝ F w) ei₀) z) ej₀ +
        Complex.I *
          (fderiv ℝ (fun w => (fderiv ℝ F w) ei₁) z) ej₀) / 2 +
      Complex.I *
        (((fderiv ℝ (fun w => (fderiv ℝ F w) ei₀) z) ej₁ +
          Complex.I *
            (fderiv ℝ (fun w => (fderiv ℝ F w) ei₁) z) ej₁) / 2)) / 2 =
    (((fderiv ℝ (fun w => (fderiv ℝ F w) ej₀) z) ei₀ +
        Complex.I *
          (fderiv ℝ (fun w => (fderiv ℝ F w) ej₁) z) ei₀) / 2 +
      Complex.I *
        (((fderiv ℝ (fun w => (fderiv ℝ F w) ej₀) z) ei₁ +
          Complex.I *
            (fderiv ℝ (fun w => (fderiv ℝ F w) ej₁) z) ei₁) / 2)) / 2
  rw [fderiv_directional_commute hF z ei₀ ej₀,
    fderiv_directional_commute hF z ei₁ ej₀,
    fderiv_directional_commute hF z ei₀ ej₁,
    fderiv_directional_commute hF z ei₁ ej₁]
  ring
end Ehrhart.TorusMollifiedBochner
