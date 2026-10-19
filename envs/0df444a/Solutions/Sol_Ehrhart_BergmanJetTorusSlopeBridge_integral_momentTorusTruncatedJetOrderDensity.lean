-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.integral_momentTorusTruncatedJetOrderDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/267fd3b7-41d6-41b6-ada6-1d09abee39c2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_integral_momentTorusRepresentative_jetBasis

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
    (∫ q : LogTorus n,
      momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
        ∑ i : Fin (bergmanDimension K k),
          (momentTruncatedJetOrder
            K hk F htransport p N i : ℝ) := by
  unfold momentTorusTruncatedJetOrderDensity
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_const_mul]
    simp only [momentTorusJetBasisWeight]
    rw [integral_momentTorusRepresentative_jetBasis]
    simp
  · intro i _
    exact
      (integrable_momentTorusRepresentative_normSq
        K hk F htransport
          (momentSimultaneousJetBasis
            K hk F htransport p i)).const_mul _
end Ehrhart.BergmanJetTorusSlopeBridge
