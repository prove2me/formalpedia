-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.eventually_integral_momentPositiveTorusJetSlope_ge_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/1dd327fc-4fae-4cc9-84c6-a40fc7b801ef

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetProfileBridge_eventually_normalizedMomentTruncatedJetOrderProfile_ge_sharp
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_integral_momentPositiveTorusJetSlope_eq_normalizedProfile

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
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ hk : 0 < k,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        ∫ q : LogTorus n,
          momentPositiveTorusJetSlope
            K hk F htransport p
            (Nat.floor
              (BodyScale.canonicalScale K * (k : ℝ))) q
          ∂(momentTorusBergmanProbability K F k) := by
  filter_upwards
    [eventually_normalizedMomentTruncatedJetOrderProfile_ge_sharp
      hn K F htransport p hε]
    with k hlower hk
  rw [integral_momentPositiveTorusJetSlope_eq_normalizedProfile
    K hk F htransport p (BodyScale.canonicalScale K)]
  exact hlower
end Ehrhart.BergmanJetTorusSlopeBridge
