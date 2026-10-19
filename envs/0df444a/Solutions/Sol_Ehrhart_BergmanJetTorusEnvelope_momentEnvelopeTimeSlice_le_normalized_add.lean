-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusEnvelope.momentEnvelopeTimeSlice_le_normalized_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/1f3c59a8-7b24-41d2-8028-45960874b6e8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetEnvelopeLimit_momentJointUpperEnvelope_le_majorant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusEnvelope
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit JetEnvelopeRightDerivative
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetTorusEnvelope
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentEnvelopeTimeSlice K F htransport p z t ≤
      momentNormalizedPotential F (realLogCoordinate z) +
        BodyScale.canonicalScale K * t := by
  rw [momentEnvelopeTimeSlice_of_positive K F htransport p z ht]
  have h := momentJointUpperEnvelope_le_majorant
    K F htransport p (sourcePositiveJointTimePoint z t ht)
  simpa [momentJointMajorant,
    jointRealCoordinate_sourcePositiveJointTimePoint,
    jointLogTime_sourcePositiveJointTimePoint] using h
end Ehrhart.BergmanJetTorusEnvelope
