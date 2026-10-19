-- Prove2me | solution 1 for Ehrhart.BergmanJetSlope.continuous_weightedDiagonalKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/2e0c8cc6-5c75-4d65-8064-b555ca395df4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSlope_continuous_normalizedMonomialDensity

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
    Continuous (BergmanMonomials.weightedDiagonalKernel K k φ) := by
  let := (BergmanMonomials.monomialIndex_finite K hk).fintype
  unfold BergmanMonomials.weightedDiagonalKernel
  simp_rw [tsum_fintype]
  exact continuous_finsetSum _
    (fun u _ => continuous_normalizedMonomialDensity K hφ u)
end Ehrhart.BergmanJetSlope
