-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusEnvelope.momentTorusEnvelopeTimeSlice_le_normalized_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/26b148bc-3401-4369-8e6e-0e61f96c2cb2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusEnvelope_momentEnvelopeTimeSlice_le_normalized_add

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
    (p : LogSpace n) (q : LogTorus n) {t : ℝ} (ht : 0 < t) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentNormalizedPotential F q.1 +
        BodyScale.canonicalScale K * t := by
  unfold momentTorusEnvelopeTimeSlice
  simpa [realLogCoordinate_sourceTorusCoverPoint] using
    momentEnvelopeTimeSlice_le_normalized_add
      K F htransport p (sourceTorusCoverPoint q) ht
end Ehrhart.BergmanJetTorusEnvelope
