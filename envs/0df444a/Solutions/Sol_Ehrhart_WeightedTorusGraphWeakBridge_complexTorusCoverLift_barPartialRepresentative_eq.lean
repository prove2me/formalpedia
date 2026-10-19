-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.complexTorusCoverLift_barPartialRepresentative_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/c6ddb5cd-9f5e-4004-a6c4-3978b44418e2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusGraphWeakBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.WeightedTorusGraphWeakBridge
theorem _root_.solution {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) :
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialRepresentative F z :
          EuclideanSpace ℂ (Fin n)) j) =
      (fun z : TorusCharacters.LogSpace n =>
        barPartialCoordinate F z j) := by
  change
    complexTorusCoverLift
      (torusScalarRepresentative
        (fun z : TorusCharacters.LogSpace n =>
          barPartialCoordinate F z j)) = _
  exact complexTorusCoverLift_torusScalarRepresentative_eq
    (fun z => barPartialCoordinate F z j)
    (fun q => barPartialCoordinate_periodic F hperiod j q)
end Ehrhart.WeightedTorusGraphWeakBridge
