-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.continuous_momentTorusTruncatedJetOrderDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/b0b80b6c-d828-4688-8466-0d8fd8d3078f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_continuous_momentTorusJetBasisWeight

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
    (p : LogSpace n) (N : ℕ) :
    Continuous
      (momentTorusTruncatedJetOrderDensity
        K hk F htransport p N) := by
  unfold momentTorusTruncatedJetOrderDensity
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.mul
      (continuous_momentTorusJetBasisWeight
        K hk F htransport p i))
end Ehrhart.BergmanJetTorusSlopeBridge
