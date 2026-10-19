-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_conj_eq_conj_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/60e71a8f-34d8-44e7-b2b0-b601a63ecfb5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_conj

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
    (hF : ContDiff ℝ 1 F)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => conj (F w)) z j =
      conj (holomorphicCoordinate F z j) := by
  unfold barPartialCoordinate holomorphicCoordinate
  rw [fderiv_conj (hF.differentiable (by simp)) z
        (Pi.single j (1 : ℂ)),
      fderiv_conj (hF.differentiable (by simp)) z
        (Pi.single j Complex.I)]
  simp only [map_div₀, map_sub, map_mul,
    Complex.conj_I, map_ofNat]
  ring
end Ehrhart.WeightedDolbeaultBochnerIdentity
