-- Prove2me | solution 1 for Ehrhart.BergmanJetPointwiseLogKernel.tendsto_log_momentNormalized_diagonalKernel_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/b959c55e-7ab8-4fd1-88b6-e5a8b7740504

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_eventually_log_momentNormalized_diagonalKernel_div_ge_sub

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPointwiseLogKernel
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability BergmanMonomials MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open MomentWeakGlobalKernel BergmanJetPhaseLaplace BergmanJetMonomialEnvelopeLower
open MomentMoserTrudinger SpatialBergmanPointwiseAsymptotics
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetPointwiseLogKernel
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x) :
    Tendsto
      (fun k : ℕ =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ))
      atTop (𝓝 (momentNormalizedPotential F x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hupper :=
    eventually_log_momentNormalized_diagonalKernel_div_le_add
      K F htransport hhalf
  have hlower :=
    eventually_log_momentNormalized_diagonalKernel_div_ge_sub
      K F htransport hu x hmax hhalf
  have hclose :
      ∀ᶠ k : ℕ in atTop,
        dist
          (Real.log
            (diagonalKernel K k
              (momentNormalizedPotential F) x) / (k : ℝ))
          (momentNormalizedPotential F x) < ε := by
    filter_upwards [hupper, hlower]
      with k hupperk hlowerk
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · linarith
    · linarith [hupperk x]
  exact Filter.eventually_atTop.mp hclose
end Ehrhart.BergmanJetPointwiseLogKernel
