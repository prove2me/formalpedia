-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.exists_open_eventual_log_momentNormalized_diagonalKernel_div_ge_sub_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/0708f2aa-1fdb-49f0-833b-041ce9995780

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_exists_open_eventual_log_momentNormalized_diagonalKernel_uniform_all

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
          momentNormalizedPotential F y - ε ≤
            Real.log
              (diagonalKernel K k
                (momentNormalizedPotential F) y) /
                  (k : ℝ) := by
  obtain ⟨U, hU, hx, huniform⟩ :=
    exists_open_eventual_log_momentNormalized_diagonalKernel_uniform_all
      K F htransport x hε
  refine ⟨U, hU, hx, ?_⟩
  filter_upwards [huniform] with k hk y hy
  have h := hk y hy
  rw [Real.dist_eq] at h
  have habs := (abs_lt.mp h).1
  linarith
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
