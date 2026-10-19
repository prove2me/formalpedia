-- Prove2me | solution 1 for Ehrhart.BergmanJetPointwiseLogKernel.exists_eventual_momentNormalized_uniform_moving_phase_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/75129745-b5ce-4220-993f-01765e881cd4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_pairing_sub_left

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
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀)) :
    ∃ d C : ℝ, 0 < d ∧
      ∀ᶠ k : ℕ in atTop, ∀ z : Space n,
        phase (u k) (momentNormalizedPotential F) z ≤
          C - d * ‖z‖ := by
  obtain ⟨δ, C, hδ, hcoerce⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu₀
  have hnorm :
      Tendsto (fun k : ℕ => ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using (hu.sub_const u₀).norm
  have hscaled :
      Tendsto (fun k : ℕ => (n : ℝ) * ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hnorm.const_mul (n : ℝ)
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * ‖u k - u₀‖ < δ / 2 :=
    hscaled (Iio_mem_nhds (half_pos hδ))
  refine ⟨δ / 2, C, half_pos hδ, ?_⟩
  filter_upwards [hsmall] with k hk z
  have hpair :
      pairing (u k - u₀) z ≤ (δ / 2) * ‖z‖ := by
    calc
      pairing (u k - u₀) z ≤ |pairing (u k - u₀) z| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖u k - u₀‖) * ‖z‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          (u k - u₀) z
      _ ≤ (δ / 2) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hk.le (norm_nonneg z)
  have hsplit :
      phase (u k) (momentNormalizedPotential F) z =
        phase u₀ (momentNormalizedPotential F) z +
          pairing (u k - u₀) z := by
    unfold phase
    rw [MonomialDivergence.pairing_sub_left]
    ring
  rw [hsplit]
  linarith [hcoerce z]
end Ehrhart.BergmanJetPointwiseLogKernel
