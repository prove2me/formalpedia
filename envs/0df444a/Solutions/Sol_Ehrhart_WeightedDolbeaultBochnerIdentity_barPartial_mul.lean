-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/9e8c4673-d011-4a67-a333-de67d686487c

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
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => F w * G w) z j =
      barPartialCoordinate F z j * G z +
        F z * barPartialCoordinate G z j := by
  have hp := fderiv_mul
    (hF.differentiable (by simp) z)
    (hG.differentiable (by simp) z)
  unfold barPartialCoordinate
  change
    ((fderiv ℝ (F * G) z) (Pi.single j (1 : ℂ)) +
      Complex.I *
        (fderiv ℝ (F * G) z) (Pi.single j Complex.I)) / 2 = _
  rw [hp]
  simp only [_root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring
end Ehrhart.WeightedDolbeaultBochnerIdentity
