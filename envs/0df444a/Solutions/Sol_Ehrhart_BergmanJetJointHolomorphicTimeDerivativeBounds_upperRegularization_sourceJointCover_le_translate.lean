-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.upperRegularization_sourceJointCover_le_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/4e02a93f-1102-4e1d-9725-1af43ed58082

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation BergmanJetEnvelopePlurisubharmonic
open BergmanJetUpperEnvelope BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative
open JetEnvelopeTrueRadialMollifier EnvelopeSmoothing EnvelopeGeneralTorusDescent
open RadialAccelerationBounds
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
theorem _root_.solution
    {n : ℕ} (f : SourceJointComplexCover n → ℝ)
    (hlocal : ∀ q : SourceJointComplexCover n,
      (localUpperBounds f q).Nonempty)
    (d : SourceJointComplexCover n)
    (hshift : ∀ q : SourceJointComplexCover n,
      f q ≤ f (q + d))
    (q : SourceJointComplexCover n) :
    upperRegularization f q ≤
      upperRegularization f (q + d) := by
  apply le_of_forall_pos_le_add
  intro η hη
  have happrox :
      ∃ c ∈ localUpperBounds f (q + d),
        c < upperRegularization f (q + d) + η := by
    unfold upperRegularization
    exact exists_lt_of_csInf_lt (hlocal (q + d))
      (lt_add_of_pos_right _ hη)
  obtain ⟨c, hc, hcη⟩ := happrox
  change
    (∀ᶠ y : SourceJointComplexCover n in 𝓝 (q + d),
      f y ≤ c) at hc
  have htranslate :
      ∀ᶠ y : SourceJointComplexCover n in 𝓝 q,
        f (y + d) ≤ c := by
    have hevent :
        ∀ᶠ y : SourceJointComplexCover n in
          𝓝 ((Homeomorph.addRight d) q), f y ≤ c := by
      simpa [Homeomorph.addRight, add_comm] using hc
    rw [← (Homeomorph.addRight d).map_nhds_eq q,
      Filter.eventually_map] at hevent
    simpa [Homeomorph.addRight, add_comm] using hevent
  have hnear :
      ∀ᶠ y : SourceJointComplexCover n in 𝓝 q,
        f y ≤ c :=
    htranslate.mono fun y hy => (hshift y).trans hy
  have hreg := upperRegularization_le_of_eventually f q hnear
  linarith
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
