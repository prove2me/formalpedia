-- Prove2me | solution 1 for Ehrhart.BergmanJetProfileBridge.eventually_normalizedMomentTruncatedJetOrderProfile_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/80d3bd44-5d68-4215-9425-b83a215d0baf

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetAsymptotics_tendsto_normalized_jetLayercake_profile
import Theorems.Thm_Ehrhart_BergmanJetProfileBridge_normalizedMomentTruncatedJetOrderProfile_ge

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
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      t - t ^ (n + 1) /
          (((n + 1).factorial : ℝ) *
            normalizedVolume K.carrier) - ε ≤
        normalizedMomentTruncatedJetOrderProfile
          K F htransport p t k := by
  have hlimit :=
    JetAsymptotics.tendsto_normalized_jetLayercake_profile K ht
  have hstrict :
      t - t ^ (n + 1) /
            (((n + 1).factorial : ℝ) *
              normalizedVolume K.carrier) - ε <
        t - t ^ (n + 1) /
          (((n + 1).factorial : ℝ) *
            normalizedVolume K.carrier) := by
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_order.mp hlimit).1 _ hstrict] with k hk hlower
  exact le_trans (le_of_lt hlower)
    (normalizedMomentTruncatedJetOrderProfile_ge K
      (lt_of_lt_of_le Nat.zero_lt_one hk) F htransport p t)
end Ehrhart.BergmanJetProfileBridge
