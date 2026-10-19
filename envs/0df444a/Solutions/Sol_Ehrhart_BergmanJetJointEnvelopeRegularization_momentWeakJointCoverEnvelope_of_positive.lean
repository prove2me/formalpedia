-- Prove2me | solution 1 for Ehrhart.BergmanJetJointEnvelopeRegularization.momentWeakJointCoverEnvelope_of_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/3b4109a7-8ff3-4e38-b7d0-16d749fd9df2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointEnvelopeRegularization
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters BergmanDiagonalBasisIndependence MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation BergmanJetEnvelopeLimit BergmanJetTorusEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology ContDiff Convolution ComplexOrder
namespace Ehrhart.BergmanJetJointEnvelopeRegularization
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourcePositiveJointTimePoint q.1
          (sourceJointCoverTime q) hq) := by
  exact momentEnvelopeTimeSlice_of_positive
    K F htransport p q.1 hq
end Ehrhart.BergmanJetJointEnvelopeRegularization
