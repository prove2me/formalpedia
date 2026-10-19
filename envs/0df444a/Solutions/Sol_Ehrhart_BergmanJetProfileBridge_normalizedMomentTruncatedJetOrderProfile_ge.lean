-- Prove2me | solution 1 for Ehrhart.BergmanJetProfileBridge.normalizedMomentTruncatedJetOrderProfile_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/d55d97f4-4326-4e8f-b9b3-a972a5f6997a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGeodesic_real_jetLayercake_le_sum_momentTruncatedJetOrder

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetProfileBridge
open Set Function Filter MeasureTheory Module InnerProductSpace
open SupportFunction BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open BergmanJetGeodesic BergmanDiagonalBasisIndependence
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology
namespace Ehrhart.BergmanJetProfileBridge
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (t : ℝ) :
    (((Nat.floor (t * (k : ℝ)) : ℕ) : ℝ) *
          (bergmanDimension K k : ℝ) -
        (((n + Nat.floor (t * (k : ℝ))).choose
          (n + 1) : ℕ) : ℝ)) /
        ((k : ℝ) * (bergmanDimension K k : ℝ)) ≤
      normalizedMomentTruncatedJetOrderProfile
        K F htransport p t k := by
  rw [normalizedMomentTruncatedJetOrderProfile, dif_pos hk]
  apply div_le_div_of_nonneg_right
  · exact real_jetLayercake_le_sum_momentTruncatedJetOrder
      K hk F htransport p (Nat.floor (t * (k : ℝ)))
  · positivity
end Ehrhart.BergmanJetProfileBridge
