-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.ae_limsup_momentTorusJetSlope_le_bodySecant_Gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/6345417d-3649-4dcf-9f05-3c58f195ea70

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_ae_limsup_momentTorusJetSlope_le_bodySecant_base

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ q : LogTorus n
      ∂(sourceProbability (momentBodyTorusWeight K p) 0),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q := by
  have hbase :=
    ae_limsup_momentTorusJetSlope_le_bodySecant_base K p ht
  change
    ∀ᵐ q : LogTorus n
      ∂((sourceTorusBaseMeasure n).withDensity
        (fun q => ENNReal.ofReal
          (sourceNormalizedDensity
            (momentBodyTorusWeight K p) 0 q))),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q
  exact (withDensity_absolutelyContinuous
    (sourceTorusBaseMeasure n)
    (fun q => ENNReal.ofReal
      (sourceNormalizedDensity
        (momentBodyTorusWeight K p) 0 q))).ae_le hbase
end Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
