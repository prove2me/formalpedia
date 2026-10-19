-- Prove2me | solution 1 for Ehrhart.BergmanJetSlope.continuous_normalizedMonomialDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/ccba36f6-ac65-47d7-8cbd-4268472c14fa

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetSlope
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.BergmanJetSlope
theorem _root_.solution {n k : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (u : LatticeAsymptotics.monomialIndex K k) :
    Continuous
      (BergmanMonomials.normalizedMonomialDensity K k φ u) := by
  unfold BergmanMonomials.normalizedMonomialDensity
  exact
    (MonomialIntegrability.continuous_monomialWeight
      (k : ℝ) (u : Space n) hφ).div_const _
end Ehrhart.BergmanJetSlope
