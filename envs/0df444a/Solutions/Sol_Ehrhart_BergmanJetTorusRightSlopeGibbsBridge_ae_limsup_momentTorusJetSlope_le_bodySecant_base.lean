-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.ae_limsup_momentTorusJetSlope_le_bodySecant_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/7fedc31e-0a83-4254-ae4b-7758ef511f9b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_ae_limsup_momentTorusJetSlope_le_envelope_positive_secant

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
    ∀ᵐ q : LogTorus n ∂(sourceTorusBaseMeasure n),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q := by
  have hrad :=
    ae_limsup_momentTorusJetSlope_le_envelope_positive_secant
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p ht
  have hprod :=
    (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Space n)))
      (ν := angularMeasure n)).ae hrad
  change
    ∀ᵐ q : LogTorus n
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n)),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q
  filter_upwards [hprod] with q hq
  simpa [momentBodyEnvelopePositiveSecant,
    momentBodyTorusWeight] using hq q.2
end Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
