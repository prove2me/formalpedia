-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.lipschitz_log_momentNormalized_diagonalKernel_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/b5798600-3493-4648-a56c-8da9746a67e2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_abs_log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius

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
      normalizedTargetBodyMeasure K) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (fun x : Space n =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h :=
    abs_log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
      K hk F htransport x y
  have hnonneg : 0 ≤ (n : ℝ) * bodyRadius K :=
    mul_nonneg (Nat.cast_nonneg n) (bodyRadius_pos K).le
  simpa [Real.dist_eq, sourceBodyLipschitzConstant,
    Real.coe_toNNReal _ hnonneg] using h
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
