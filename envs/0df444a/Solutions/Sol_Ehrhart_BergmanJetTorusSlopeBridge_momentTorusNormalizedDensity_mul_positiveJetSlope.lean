-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.momentTorusNormalizedDensity_mul_positiveJetSlope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/be526267-4a98-4163-8e05-eccd63f77bb8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    (diagonalKernel K k (momentNormalizedPotential F) q.1 /
      (bergmanDimension K k : ℝ)) *
        momentPositiveTorusJetSlope
          K hk F htransport p N q =
      momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q /
          ((k : ℝ) * (bergmanDimension K k : ℝ)) := by
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  have hdim : (bergmanDimension K k : ℝ) ≠ 0 := by
    exact_mod_cast (bergmanDimension_pos K hk).ne'
  have hdiag :
      diagonalKernel K k (momentNormalizedPotential F) q.1 ≠ 0 :=
    (diagonalKernel_momentNormalized_pos
      K hk F htransport q.1).ne'
  unfold momentPositiveTorusJetSlope
  field_simp
end Ehrhart.BergmanJetTorusSlopeBridge
