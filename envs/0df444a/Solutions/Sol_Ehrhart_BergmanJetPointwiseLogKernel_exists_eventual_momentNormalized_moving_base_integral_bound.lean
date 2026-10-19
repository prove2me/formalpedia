-- Prove2me | solution 1 for Ehrhart.BergmanJetPointwiseLogKernel.exists_eventual_momentNormalized_moving_base_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/151a23da-c2e8-4bea-ae79-c152da2db5b2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_exists_eventual_momentNormalized_uniform_moving_phase_coercivity

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
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ k : ℕ in atTop,
        monomialIntegral 1 (u k)
          (momentNormalizedPotential F) ≤ B := by
  obtain ⟨d, C, hd, hcoerce⟩ :=
    exists_eventual_momentNormalized_uniform_moving_phase_coercivity
      K F htransport hu₀ u hu
  have hrad := integrable_exp_neg_mul_norm_all (n := n) hd
  let B : ℝ := max 1
    (Real.exp C *
      (∫ z : Space n,
        Real.exp (-d * ‖z‖)
          ∂(volume : Measure (Space n))))
  have hB : 0 < B :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hcoerce, hinterior] with k hk hku
  calc
    monomialIntegral 1 (u k)
        (momentNormalizedPotential F) ≤
      ∫ z : Space n,
        Real.exp C * Real.exp (-d * ‖z‖)
          ∂(volume : Measure (Space n)) := by
      unfold monomialIntegral
      apply MeasureTheory.integral_mono
        (integrable_monomialWeight_momentNormalized_of_mem_interior
          F htransport hku zero_lt_one)
        (hrad.const_mul (Real.exp C))
      intro z
      unfold monomialWeight
      simp only [one_mul]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hk z
      unfold phase at h
      linarith
    _ = Real.exp C *
        (∫ z : Space n,
          Real.exp (-d * ‖z‖)
            ∂(volume : Measure (Space n))) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ B := le_max_right _ _
end Ehrhart.BergmanJetPointwiseLogKernel
