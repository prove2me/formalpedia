-- Prove2me | solution 1 for Ehrhart.BergmanJetSlope.continuous_normalizedDiagonalDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/67aa7b19-cf91-4521-9509-b6a27fb963c8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSlope_continuous_weightedDiagonalKernel

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
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous
      (BergmanNormalization.normalizedDiagonalDensity K k φ) := by
  unfold BergmanNormalization.normalizedDiagonalDensity
  exact (continuous_weightedDiagonalKernel K hk hφ).div_const _
end Ehrhart.BergmanJetSlope
