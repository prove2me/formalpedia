-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.continuous_momentTorusJetBasisWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/3f97a68d-61ed-483c-91e8-9c78abdeb797

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
    (p : LogSpace n) (i : Fin (bergmanDimension K k)) :
    Continuous (fun q : LogTorus n =>
      momentTorusJetBasisWeight K hk F htransport p q i) := by
  unfold momentTorusJetBasisWeight
  exact Complex.continuous_normSq.comp
    (continuous_momentTorusRepresentative K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p i))
end Ehrhart.BergmanJetTorusSlopeBridge
