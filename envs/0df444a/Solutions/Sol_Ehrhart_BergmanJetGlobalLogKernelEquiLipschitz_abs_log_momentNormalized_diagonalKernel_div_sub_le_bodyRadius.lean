-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.abs_log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/f59c9c2b-bfc0-410e-b7cb-6dbc7a105373

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x y : Space n) :
    |Real.log
        (diagonalKernel K k (momentNormalizedPotential F) x) /
          (k : ℝ) -
      Real.log
        (diagonalKernel K k (momentNormalizedPotential F) y) /
          (k : ℝ)| ≤
      ((n : ℝ) * bodyRadius K) * dist x y := by
  apply abs_le.mpr
  constructor
  · have h :=
      log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
        K hk F htransport y x
    rw [dist_comm y x] at h
    linarith
  · exact
      log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
        K hk F htransport x y
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
