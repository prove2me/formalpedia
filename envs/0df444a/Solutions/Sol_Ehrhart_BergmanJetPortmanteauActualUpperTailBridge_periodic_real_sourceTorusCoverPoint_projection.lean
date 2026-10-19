-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.periodic_real_sourceTorusCoverPoint_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/c38d3abc-211e-4471-94e1-7579e2626b39

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (hf : ∀ m : Fin n → ℤ,
      Function.Periodic f (imaginaryShift m))
    (z : LogSpace n) :
    f (sourceTorusCoverPoint
      (complexTorusCoverProjection n z)) = f z := by
  have hcperiod : ∀ m : Fin n → ℤ,
      Function.Periodic (fun w : LogSpace n => (f w : ℂ))
        (imaginaryShift m) := by
    intro m w
    exact congrArg (fun a : ℝ => (a : ℂ)) (hf m w)
  have hc := congrFun
    (complexTorusCoverLift_torusScalarRepresentative_eq
      (fun w : LogSpace n => (f w : ℂ)) hcperiod) z
  change
    (f (sourceTorusCoverPoint
      (complexTorusCoverProjection n z)) : ℂ) = (f z : ℂ)
    at hc
  exact congrArg Complex.re hc
end Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
