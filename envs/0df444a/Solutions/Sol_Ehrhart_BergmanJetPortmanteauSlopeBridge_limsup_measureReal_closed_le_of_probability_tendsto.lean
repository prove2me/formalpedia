-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauSlopeBridge.limsup_measureReal_closed_le_of_probability_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/28661c74-52bd-4b94-b4db-01df387b3d2d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauSlopeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauSlopeBridge
theorem _root_.solution
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ProbabilityMeasure X) (μk : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μk atTop (𝓝 μ))
    {S : Set X} (hS : IsClosed S) :
    Filter.limsup
        (fun k : ℕ => (μk k : Measure X).real S) atTop ≤
      (μ : Measure X).real S := by
  have hclosed :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hS
  have hbound :
      ∀ᶠ k : ℕ in atTop, (μk k : Measure X) S ≤ (1 : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun k =>
      @prob_le_one X _ (μk k : Measure X) inferInstance S
  change
    Filter.limsup
        (fun k : ℕ => ((μk k : Measure X) S).toReal) atTop ≤
      ((μ : Measure X) S).toReal
  rw [ENNReal.limsup_toReal_eq ENNReal.one_ne_top hbound]
  exact ENNReal.toReal_mono (measure_ne_top (μ : Measure X) S) hclosed
end Ehrhart.BergmanJetPortmanteauSlopeBridge
