-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceUnitAngularHaar_eq_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/7dc1c6ab-94f8-47e2-a4df-307f41fb09da

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v
namespace Ehrhart.JetEnvelopeLocalGrowth
theorem _root_.solution :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) =
      (volume : Measure UnitAddCircle) := by
  simpa using
    (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
end Ehrhart.JetEnvelopeLocalGrowth
