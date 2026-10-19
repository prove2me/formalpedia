-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.tendsto_log_momentNormalized_diagonalKernel_div_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/5e840161-2430-4cc4-8b3a-9c51ddec5cce

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_tendsto_log_momentNormalized_diagonalKernel_div
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_lipschitz_log_momentNormalized_diagonalKernel_div
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_dense_finiteEnergySourceInteriorDifferentiability
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_tendsto_of_dense_eventually_equiLipschitz
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_finiteEnergySourceNormalized_actualGradient_phase_max

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
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    Tendsto
      (fun k : ℕ =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ))
      atTop (𝓝 (momentNormalizedPotential F x)) := by
  let f : ℕ → Space n → ℝ :=
    fun k y =>
      Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) y) / (k : ℝ)
  let S : Set (Space n) :=
    {y : Space n |
      DifferentiableAt ℝ
          (F.potential : Space n → ℝ) y ∧
        SpatialBergmanFatouScheffe.actualGradient
          F.potential y ∈ interior K.carrier}
  have hf : ∀ᶠ k : ℕ in atTop,
      LipschitzWith (sourceBodyLipschitzConstant K) (f k) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact lipschitz_log_momentNormalized_diagonalKernel_div
      K hk F htransport
  have hS : Dense S :=
    dense_finiteEnergySourceInteriorDifferentiability
      K F htransport
  have hconv : ∀ y ∈ S,
      Tendsto (fun k : ℕ => f k y)
        atTop (𝓝 (momentNormalizedPotential F y)) := by
    intro y hy
    exact tendsto_log_momentNormalized_diagonalKernel_div
      K F htransport hy.2 y
      (finiteEnergySourceNormalized_actualGradient_phase_max
        F y hy.1)
  exact tendsto_of_dense_eventually_equiLipschitz
    f (momentNormalizedPotential F)
    (sourceBodyLipschitzConstant K) hf
    (lipschitz_momentNormalizedPotential F)
    hS hconv x
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
