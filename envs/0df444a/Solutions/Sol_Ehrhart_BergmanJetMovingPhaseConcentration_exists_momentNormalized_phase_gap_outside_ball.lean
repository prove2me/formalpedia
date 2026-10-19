-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingPhaseConcentration.exists_momentNormalized_phase_gap_outside_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/8f5d9e79-7d4b-4951-a5e6-50a884113a5f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDualPhaseConcentration_finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
import Theorems.Thm_Ehrhart_BergmanJetDualPhaseConcentration_momentNormalized_phaseMaximizer_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetPhaseLaplace
open BergmanJetDualPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingPhaseConcentration
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) x₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : Space n,
      x ∉ Metric.ball x₀ r →
        phase u (momentNormalizedPotential F) x ≤
          phase u (momentNormalizedPotential F) x₀ - η := by
  obtain ⟨δ, C, hδ, hcoercive⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu
  let R : ℝ :=
    max 0 ((C - phase u (momentNormalizedPotential F) x₀ + 1) / δ)
  have houter : ∀ x : Space n,
      x ∉ Metric.closedBall (0 : Space n) R →
        phase u (momentNormalizedPotential F) x ≤
          phase u (momentNormalizedPotential F) x₀ - 1 := by
    intro x hx
    have hxnorm : R < ‖x‖ := by
      apply lt_of_not_ge
      intro h
      apply hx
      simpa [Metric.mem_closedBall] using h
    have hR :
        C - phase u (momentNormalizedPotential F) x₀ + 1 ≤
          δ * R := by
      have hle :
          (C - phase u (momentNormalizedPotential F) x₀ + 1) / δ ≤ R :=
        le_max_right _ _
      simpa [mul_comm] using (div_le_iff₀ hδ).mp hle
    have hscale := mul_lt_mul_of_pos_left hxnorm hδ
    have hcoerce := hcoercive x
    nlinarith
  let t : Set (Space n) :=
    Metric.closedBall (0 : Space n) R ∩
      (Metric.ball x₀ r)ᶜ
  have htcompact : IsCompact t := by
    exact (isCompact_closedBall (0 : Space n) R).inter_right
      Metric.isOpen_ball.isClosed_compl
  by_cases ht : t.Nonempty
  · obtain ⟨z, hz, hzmax⟩ :=
      htcompact.exists_isMaxOn ht
        (continuous_phase u
          (continuous_momentNormalizedPotential F)).continuousOn
    have hzout : z ∉ Metric.ball x₀ r := hz.2
    have hzne : z ≠ x₀ := by
      intro heq
      subst z
      exact hzout (Metric.mem_ball_self hr)
    have hznephase :
        phase u (momentNormalizedPotential F) z ≠
          phase u (momentNormalizedPotential F) x₀ := by
      intro heq
      have hzglobal : ∀ y : Space n,
          phase u (momentNormalizedPotential F) y ≤
            phase u (momentNormalizedPotential F) z := by
        intro y
        rw [heq]
        exact hmax y
      have hxdual := finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
        F htransport hu hdu x₀
        ((momentNormalized_phaseMaximizer_iff F u x₀).mp hmax)
      have hzdual := finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
        F htransport hu hdu z
        ((momentNormalized_phaseMaximizer_iff F u z).mp hzglobal)
      exact hzne (hxdual.symm.trans hzdual).symm
    have hzlt :
        phase u (momentNormalizedPotential F) z <
          phase u (momentNormalizedPotential F) x₀ :=
      lt_of_le_of_ne (hmax z) hznephase
    let η : ℝ :=
      min 1 (phase u (momentNormalizedPotential F) x₀ -
        phase u (momentNormalizedPotential F) z)
    have hη : 0 < η :=
      lt_min zero_lt_one (sub_pos.mpr hzlt)
    refine ⟨η, hη, fun x hx => ?_⟩
    by_cases hxR : x ∈ Metric.closedBall (0 : Space n) R
    · have hxt : x ∈ t := ⟨hxR, hx⟩
      have hzx :
          phase u (momentNormalizedPotential F) x ≤
            phase u (momentNormalizedPotential F) z := hzmax hxt
      have hηle :
          η ≤ phase u (momentNormalizedPotential F) x₀ -
            phase u (momentNormalizedPotential F) z :=
        min_le_right _ _
      linarith
    · have hout := houter x hxR
      have hηle : η ≤ (1 : ℝ) := min_le_left _ _
      linarith
  · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
    apply houter x
    intro hxR
    exact ht ⟨x, hxR, hx⟩
end Ehrhart.BergmanJetMovingPhaseConcentration
