-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.complexContinuousOfCoordinateCR_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/71ff0f55-d1d9-499a-9758-73d09c43cc59

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultRegularity
theorem _root_.solution {n : ℕ}
    (D : TorusCharacters.LogSpace n →L[ℝ] ℂ)
    (hI : ∀ j : Fin n,
      D (Pi.single j Complex.I) =
        Complex.I • D (Pi.single j (1 : ℂ))) :
    (complexContinuousOfCoordinateCR D hI).restrictScalars ℝ = D := by
  ext x
  rfl
end Ehrhart.DolbeaultRegularity
