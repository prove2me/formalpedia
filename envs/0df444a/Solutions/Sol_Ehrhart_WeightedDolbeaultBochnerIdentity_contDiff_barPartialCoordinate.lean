-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.contDiff_barPartialCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/f0c64b5c-796b-418e-b35c-ddd6a8178ebb

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
    (j : Fin n) :
    ContDiff ℝ 1 (fun z => barPartialCoordinate F z j) := by
  unfold barPartialCoordinate
  exact ((contDiff_directional hF (Pi.single j (1 : ℂ))).add
    (contDiff_const.mul
      (contDiff_directional hF (Pi.single j Complex.I)))).div_const 2
end Ehrhart.WeightedDolbeaultBochnerIdentity
