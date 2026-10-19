-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.moment_diagonalKernel_le_exp_bodyRadius_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/f79751ad-38d3-42a6-8807-94911b85b3e7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_moment_diagonalTerm_le_exp_bodyRadius_mul

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
    diagonalKernel K k (momentNormalizedPotential F) x ≤
      Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        diagonalKernel K k (momentNormalizedPotential F) y := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold diagonalKernel
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ =>
    moment_diagonalTerm_le_exp_bodyRadius_mul
      K hk F htransport u x y
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
