-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.fderiv_barPartialCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/2072b7ad-d126-4ec4-88c1-b2ab77c7b33d

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
    (hF : ContDiff ℝ 2 F)
    (z v : TorusCharacters.LogSpace n)
    (j : Fin n) :
    (fderiv ℝ
      (fun w => barPartialCoordinate F w j) z) v =
      ((fderiv ℝ
        (fun w => (fderiv ℝ F w) (Pi.single j (1 : ℂ))) z) v +
        Complex.I *
          (fderiv ℝ
            (fun w =>
              (fderiv ℝ F w) (Pi.single j Complex.I)) z) v) / 2 := by
  let e₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let e₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have h₀ := (contDiff_directional hF e₀).differentiable
    (by simp) z
  have h₁ := (contDiff_directional hF e₁).differentiable
    (by simp) z
  have hd := (h₀.hasFDerivAt.add
    (h₁.hasFDerivAt.const_mul Complex.I)).mul_const
      ((2 : ℂ)⁻¹)
  have hp := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D v)
      hd.fderiv
  simpa only [barPartialCoordinate, e₀, e₁, div_eq_mul_inv,
    Pi.add_apply,
    _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, mul_comm] using hp
end Ehrhart.WeightedDolbeaultBochnerIdentity
