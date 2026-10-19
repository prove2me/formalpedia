-- Prove2me | solution 1 for Ehrhart.BergmanJetPointwiseLogKernel.eventually_log_momentNormalized_diagonalKernel_div_ge_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/dbbbef3d-8803-447f-9d7a-9d9530b85788

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SpatialBergmanPointwiseAsymptotics_tendsto_nearestMonomialIndex
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_eventually_log_momentNormalized_moving_monomialIntegral_div_le

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
        phase u (momentNormalizedPotential F) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      momentNormalizedPotential F x - ε ≤
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ) := by
  let v : ℕ → Space n :=
    fun k => (nearestMonomialIndex K u k : Space n)
  have hv : Tendsto v atTop (𝓝 u) :=
    tendsto_nearestMonomialIndex K hu
  have hpair :
      Tendsto
        (fun k : ℕ => pairing (v k) x)
        atTop (𝓝 (pairing u x)) :=
    (continuous_pairing_left x).continuousAt.tendsto.comp hv
  have hpairlower :
      ∀ᶠ k : ℕ in atTop,
        pairing u x - ε / 2 < pairing (v k) x := by
    exact hpair (Ioi_mem_nhds (by linarith))
  have hphase :=
    eventually_log_momentNormalized_moving_monomialIntegral_div_le
      K F htransport hu v hv x hmax (half_pos hε)
  filter_upwards
    [eventually_ge_atTop (1 : ℕ), hpairlower, hphase]
    with k hk hpairk hphasek
  have hkpos : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one hk
  have hdiag :=
    moment_pairing_sub_log_monomialNorm_le_log_diagonal
      K hkpos F htransport (nearestMonomialIndex K u k) x
  change
    pairing (v k) x -
        Real.log
          (monomialIntegral (k : ℝ) (v k)
            (momentNormalizedPotential F)) / (k : ℝ) ≤
      Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) x) / (k : ℝ)
    at hdiag
  unfold phase at hphasek
  linarith
end Ehrhart.BergmanJetPointwiseLogKernel
