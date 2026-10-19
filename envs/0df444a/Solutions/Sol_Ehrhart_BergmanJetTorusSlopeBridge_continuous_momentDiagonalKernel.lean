-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.continuous_momentDiagonalKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/b49e0ecc-d429-4622-b763-ed15a2967d0f

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
    (F : SourceFiniteEnergyPotential K) :
    Continuous (diagonalKernel K k (momentNormalizedPotential F)) := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold diagonalKernel
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro u _
  unfold diagonalTerm SupportFunction.pairing
  fun_prop
end Ehrhart.BergmanJetTorusSlopeBridge
