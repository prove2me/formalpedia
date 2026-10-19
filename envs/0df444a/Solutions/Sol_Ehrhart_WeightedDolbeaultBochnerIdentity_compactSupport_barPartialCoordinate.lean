-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.compactSupport_barPartialCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/2de53154-35d0-45c9-9cff-0f98849fbf91

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (hF : HasCompactSupport F)
    (j : Fin n) :
    HasCompactSupport (fun z => barPartialCoordinate F z j) := by
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have hs : HasCompactSupport
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v₀ + Complex.I * (fderiv ℝ F z) v₁) := by
    exact (hF.fderiv_apply ℝ v₀).add
      ((hF.fderiv_apply ℝ v₁).mul_left)
  have hp := hs.mul_right
    (f' := fun _ : TorusCharacters.LogSpace n =>
      ((2 : ℂ)⁻¹))
  unfold barPartialCoordinate
  change HasCompactSupport
    ((fun z : TorusCharacters.LogSpace n =>
      (fderiv ℝ F z) v₀ + Complex.I * (fderiv ℝ F z) v₁) *
      fun _ : TorusCharacters.LogSpace n => (2 : ℂ)⁻¹)
  exact hp
end Ehrhart.WeightedDolbeaultBochnerIdentity
