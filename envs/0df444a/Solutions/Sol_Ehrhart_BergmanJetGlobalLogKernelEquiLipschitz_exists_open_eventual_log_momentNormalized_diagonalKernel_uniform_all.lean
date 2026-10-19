-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.exists_open_eventual_log_momentNormalized_diagonalKernel_uniform_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/fd2b643d-efea-4928-8b6c-4d0699000843

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_lipschitz_log_momentNormalized_diagonalKernel_div
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_tendsto_log_momentNormalized_diagonalKernel_div_all
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_exists_open_eventual_uniform_of_equiLipschitz

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
    (x : Space n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (Space n),
      IsOpen U ∧ x ∈ U ∧
        ∀ᶠ k : ℕ in atTop, ∀ y ∈ U,
          dist
            (Real.log
              (diagonalKernel K k
                (momentNormalizedPotential F) y) /
                  (k : ℝ))
            (momentNormalizedPotential F y) < ε := by
  let f : ℕ → Space n → ℝ :=
    fun k y =>
      Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) y) / (k : ℝ)
  have hf : ∀ᶠ k : ℕ in atTop,
      LipschitzWith (sourceBodyLipschitzConstant K) (f k) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact lipschitz_log_momentNormalized_diagonalKernel_div
      K hk F htransport
  exact exists_open_eventual_uniform_of_equiLipschitz
    f (momentNormalizedPotential F)
    (sourceBodyLipschitzConstant K) hf
    (lipschitz_momentNormalizedPotential F) x
    (tendsto_log_momentNormalized_diagonalKernel_div_all
      K F htransport x) hε
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
