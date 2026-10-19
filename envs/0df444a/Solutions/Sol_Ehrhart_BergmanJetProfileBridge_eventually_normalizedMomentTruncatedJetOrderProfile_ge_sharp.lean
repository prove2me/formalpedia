-- Prove2me | solution 1 for Ehrhart.BergmanJetProfileBridge.eventually_normalizedMomentTruncatedJetOrderProfile_ge_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/1965c82b-3a72-45ee-a2eb-05fc6e7401cb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BodyScale_canonicalScale_pow
import Theorems.Thm_Ehrhart_JetAsymptotics_normalized_jetLayercake_value_at_bodyScale
import Theorems.Thm_Ehrhart_BergmanJetProfileBridge_eventually_normalizedMomentTruncatedJetOrderProfile_ge

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
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        normalizedMomentTruncatedJetOrderProfile
          K F htransport p
          (BodyScale.canonicalScale K) k := by
  have h := eventually_normalizedMomentTruncatedJetOrderProfile_ge
    K F htransport p (BodyScale.canonicalScale_pos K) hε
  simpa [JetAsymptotics.normalized_jetLayercake_value_at_bodyScale
    K (BodyScale.canonicalScale_pow hn K)] using h
end Ehrhart.BergmanJetProfileBridge
