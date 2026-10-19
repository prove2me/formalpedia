-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialTailConvergence.exists_eventual_momentNormalized_moving_off_ball_exponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/01dbd8af-dc32-413b-b40f-e1632c72b3c4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_exists_eventual_momentNormalized_moving_base_integral_bound
import Theorems.Thm_Ehrhart_BergmanJetMovingPhaseConcentration_momentNormalized_off_phase_setIntegral_le_exp_mul_base
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialConcentration_exists_eventual_momentNormalized_moving_phase_gap_outside_ball
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialProbability_exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingMonomialTailConvergence
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetPointwiseLogKernel
open BergmanJetMovingPhaseConcentration BergmanJetMovingMonomialConcentration
open BergmanJetMovingMonomialProbability
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingMonomialTailConvergence
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
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ᶠ k : ℕ in atTop,
        (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
          monomialWeight (k : ℝ) (u k)
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
            monomialIntegral (k : ℝ) (u k)
              (momentNormalizedPotential F) ≤
          A * Real.exp (-((k : ℝ) * (η / 2))) := by
  let φ : Space n → ℝ := momentNormalizedPotential F
  obtain ⟨η, hη, hgap⟩ :=
    exists_eventual_momentNormalized_moving_phase_gap_outside_ball
      F htransport hu₀ hdu₀ x₀ hmax u hu hr
  obtain ⟨ρ, hρ, hvol, hden⟩ :=
    exists_eventual_momentNormalized_moving_ball_volume_exp_le_monomialIntegral
      F htransport hu₀ u hu x₀ (half_pos hη)
  obtain ⟨B, hB, hbase⟩ :=
    exists_eventual_momentNormalized_moving_base_integral_bound
      K F htransport hu₀ u hu
  let V : ℝ :=
    (volume : Measure (Space n)).real
      (Metric.ball x₀ ρ)
  let P₀ : ℝ := phase u₀ φ x₀
  let A : ℝ := (B / V) * Real.exp (η + 1 - P₀)
  have hV : 0 < V := hvol
  have hA : 0 < A :=
    mul_pos (div_pos hB hV) (Real.exp_pos _)
  have hptendsto :
      Tendsto (fun k : ℕ => phase (u k) φ x₀)
        atTop (𝓝 P₀) := by
    simpa [phase, P₀] using
      (((continuous_pairing_left x₀).continuousAt.tendsto.comp hu).sub_const
        (φ x₀))
  have hplower :
      ∀ᶠ k : ℕ in atTop,
        P₀ - 1 < phase (u k) φ x₀ :=
    hptendsto (Ioi_mem_nhds (by linarith))
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  refine ⟨A, η, hA, hη, ?_⟩
  filter_upwards [hgap, hden, hbase, hplower, hinterior,
    eventually_ge_atTop (1 : ℕ)]
    with k hkgap hkden hkbase hkp hkint hkone
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hkone
  have hkpos : 0 < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkreal
  have hnum :=
    momentNormalized_off_phase_setIntegral_le_exp_mul_base
      F htransport hkint Metric.isOpen_ball.measurableSet.compl
      hkgap hkreal
  have hupper :
      (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
        monomialWeight (k : ℝ) (u k) φ x
        ∂(volume : Measure (Space n))) ≤
          Real.exp
            (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) * B := by
    calc
      (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
        monomialWeight (k : ℝ) (u k) φ x
        ∂(volume : Measure (Space n))) ≤
          Real.exp
            (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) *
              monomialIntegral 1 (u k) φ := hnum
      _ ≤ Real.exp
            (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) * B :=
        mul_le_mul_of_nonneg_left hkbase (Real.exp_pos _).le
  have hden' :
      V * Real.exp
          ((k : ℝ) * (phase (u k) φ x₀ - η / 2)) ≤
        monomialIntegral (k : ℝ) (u k) φ :=
    hkden hkpos
  have hquot :=
    div_le_div₀
      (mul_nonneg (Real.exp_pos _).le hB.le)
      hupper
      (mul_pos hV (Real.exp_pos _))
      hden'
  calc
    (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
      monomialWeight (k : ℝ) (u k) φ x
      ∂(volume : Measure (Space n))) /
        monomialIntegral (k : ℝ) (u k) φ ≤
      (Real.exp
        (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) * B) /
        (V * Real.exp
          ((k : ℝ) * (phase (u k) φ x₀ - η / 2))) := hquot
    _ = (B / V) *
        (Real.exp
          (((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) /
          Real.exp
            ((k : ℝ) * (phase (u k) φ x₀ - η / 2))) := by
      field_simp
    _ = (B / V) *
        Real.exp
          ((((k : ℝ) - 1) * (phase (u k) φ x₀ - η)) -
            (k : ℝ) * (phase (u k) φ x₀ - η / 2)) := by
      rw [Real.exp_sub]
    _ = (B / V) *
        Real.exp
          ((η - phase (u k) φ x₀) +
            (-((k : ℝ) * (η / 2)))) := by
      congr 2
      ring
    _ = ((B / V) * Real.exp (η - phase (u k) φ x₀)) *
          Real.exp (-((k : ℝ) * (η / 2))) := by
      rw [Real.exp_add]
      ring
    _ ≤ ((B / V) * Real.exp (η + 1 - P₀)) *
          Real.exp (-((k : ℝ) * (η / 2))) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (div_pos hB hV).le
      apply Real.exp_le_exp.mpr
      linarith
    _ = A * Real.exp (-((k : ℝ) * (η / 2))) := rfl
end Ehrhart.BergmanJetMovingMonomialTailConvergence
