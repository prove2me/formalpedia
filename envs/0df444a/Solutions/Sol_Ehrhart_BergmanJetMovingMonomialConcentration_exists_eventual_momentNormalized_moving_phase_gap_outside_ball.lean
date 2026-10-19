-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialConcentration.exists_eventual_momentNormalized_moving_phase_gap_outside_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/86614fb0-1c1e-4e93-8c94-bcb8160d77d2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetMovingPhaseConcentration_exists_momentNormalized_phase_gap_outside_ball
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialConcentration_concaveOn_momentNormalized_phase
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialConcentration_concave_radial_gap_of_off_ball

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingMonomialConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentWeakBergman BergmanJetMovingPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingMonomialConcentration
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (hdu₀ : DifferentiableAt ℝ (legendreTransform F.potential) u₀)
    (x₀ : Space n)
    (hmax : ∀ x : Space n,
      phase u₀ (momentNormalizedPotential F) x ≤
        phase u₀ (momentNormalizedPotential F) x₀)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
        x ∉ Metric.ball x₀ r →
          phase (u k) (momentNormalizedPotential F) x ≤
            phase (u k) (momentNormalizedPotential F) x₀ - η := by
  obtain ⟨η, hη, hgap⟩ :=
    exists_momentNormalized_phase_gap_outside_ball
      F htransport hu₀ hdu₀ x₀ hmax (half_pos hr)
  have hnorm :
      Tendsto
        (fun k : ℕ => (n : ℝ) * ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using ((hu.sub_const u₀).norm).const_mul (n : ℝ)
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * ‖u k - u₀‖ < η / r :=
    hnorm (Iio_mem_nhds (div_pos hη hr))
  refine ⟨η, hη, ?_⟩
  filter_upwards [hsmall] with k hk x hx
  have hdist : r ≤ ‖x - x₀‖ := by
    have hd : r ≤ dist x x₀ := by
      exact le_of_not_gt (by simpa [Metric.mem_ball] using hx)
    simpa [dist_eq_norm] using hd
  have hradial := concave_radial_gap_of_off_ball
    (concaveOn_momentNormalized_phase F u₀)
    x₀ (half_pos hr) hgap x (le_trans (by linarith) hdist)
  have hpert :
      pairing (u k - u₀) (x - x₀) ≤
        (η / r) * ‖x - x₀‖ := by
    calc
      pairing (u k - u₀) (x - x₀) ≤
          |pairing (u k - u₀) (x - x₀)| := le_abs_self _
      _ ≤ ((n : ℝ) * ‖u k - u₀‖) * ‖x - x₀‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          (u k - u₀) (x - x₀)
      _ ≤ (η / r) * ‖x - x₀‖ :=
        mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)
  have hsplit :
      phase (u k) (momentNormalizedPotential F) x -
          phase (u k) (momentNormalizedPotential F) x₀ =
        (phase u₀ (momentNormalizedPotential F) x -
          phase u₀ (momentNormalizedPotential F) x₀) +
            pairing (u k - u₀) (x - x₀) := by
    simp only [phase, pairing, Pi.sub_apply, sub_mul, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hscale : (η / r) * ‖x - x₀‖ ≥ η := by
    have hq : 0 ≤ η / r := (div_pos hη hr).le
    calc
      η = (η / r) * r := (div_mul_cancel₀ η hr.ne').symm
      _ ≤ (η / r) * ‖x - x₀‖ :=
        mul_le_mul_of_nonneg_left hdist hq
  have hhalf : η / (r / 2) = 2 * (η / r) := by
    field_simp
  rw [hhalf] at hradial
  linarith
end Ehrhart.BergmanJetMovingMonomialConcentration
