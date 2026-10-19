-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_holomorphic_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/45f66150-5d0f-457c-a463-3d80327c82b1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_directional_commute
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_holomorphicCoordinate
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_barPartialCoordinate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate
namespace Ehrhart.WeightedDolbeaultBochnerIdentity
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    barPartialCoordinate
      (fun w => holomorphicCoordinate F w i) z j =
    holomorphicCoordinate
      (fun w => barPartialCoordinate F w j) z i := by
  let eᵢ₀ : TorusCharacters.LogSpace n :=
    Pi.single i (1 : ℂ)
  let eᵢ₁ : TorusCharacters.LogSpace n :=
    Pi.single i Complex.I
  let eⱼ₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let eⱼ₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  change
    ((fderiv ℝ (fun w => holomorphicCoordinate F w i) z) eⱼ₀ +
      Complex.I *
        (fderiv ℝ (fun w => holomorphicCoordinate F w i) z) eⱼ₁) / 2 =
    ((fderiv ℝ (fun w => barPartialCoordinate F w j) z) eᵢ₀ -
      Complex.I *
        (fderiv ℝ (fun w => barPartialCoordinate F w j) z) eᵢ₁) / 2
  rw [fderiv_holomorphicCoordinate hF z eⱼ₀ i,
    fderiv_holomorphicCoordinate hF z eⱼ₁ i,
    fderiv_barPartialCoordinate hF z eᵢ₀ j,
    fderiv_barPartialCoordinate hF z eᵢ₁ j]
  rw [fderiv_directional_commute hF z eᵢ₀ eⱼ₀,
    fderiv_directional_commute hF z eᵢ₁ eⱼ₀,
    fderiv_directional_commute hF z eᵢ₀ eⱼ₁,
    fderiv_directional_commute hF z eᵢ₁ eⱼ₁]
  ring
end Ehrhart.WeightedDolbeaultBochnerIdentity
