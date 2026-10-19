-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.integral_momentPositiveTorusJetSlope_eq_normalizedProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/faf30bf5-ed7a-41d7-b3b7-309284f451d8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_integral_momentPositiveTorusJetSlope

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusSlopeBridge
open Set Function Filter MeasureTheory Module InnerProductSpace
open TorusCharacters WeightedTorusHilbert BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge JetEnvelopeRightDerivative
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetTorusSlopeBridge
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      momentPositiveTorusJetSlope
        K hk F htransport p (Nat.floor (t * (k : ℝ))) q
        ∂(momentTorusBergmanProbability K F k)) =
      normalizedMomentTruncatedJetOrderProfile
        K F htransport p t k := by
  rw [integral_momentPositiveTorusJetSlope]
  simp [normalizedMomentTruncatedJetOrderProfile, hk]
end Ehrhart.BergmanJetTorusSlopeBridge
