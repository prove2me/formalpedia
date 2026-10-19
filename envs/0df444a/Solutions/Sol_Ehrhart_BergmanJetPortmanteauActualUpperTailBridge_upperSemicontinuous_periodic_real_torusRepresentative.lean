-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.upperSemicontinuous_periodic_real_torusRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/94548d49-e169-408b-99d4-669ffd4999a7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauSlopeBridge_upperSemicontinuous_of_complexTorusCover
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualUpperTailBridge_periodic_real_sourceTorusCoverPoint_projection

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge JetEnvelopeRightDerivative EnvelopeSpatialPeriodicity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation BergmanJetUpperEnvelope
open BergmanJetSpatialPeriodicity BergmanJetPortmanteauSlopeBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
theorem _root_.solution
    {n : ℕ} (f : LogSpace n → ℝ)
    (hfperiod : ∀ m : Fin n → ℤ,
      Function.Periodic f (imaginaryShift m))
    (hf : UpperSemicontinuous f) :
    UpperSemicontinuous
      (fun q : LogTorus n => f (sourceTorusCoverPoint q)) := by
  apply upperSemicontinuous_of_complexTorusCover
  have heq :
      (fun z : LogSpace n =>
        f (sourceTorusCoverPoint
          (complexTorusCoverProjection n z))) = f := by
    funext z
    exact periodic_real_sourceTorusCoverPoint_projection
      f hfperiod z
  rw [heq]
  exact hf
end Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
