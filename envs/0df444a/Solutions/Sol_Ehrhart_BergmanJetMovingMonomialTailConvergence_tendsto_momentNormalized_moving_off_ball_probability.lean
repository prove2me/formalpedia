-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialTailConvergence.tendsto_momentNormalized_moving_off_ball_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/d9f29949-32c6-46db-a108-0e6f52ac0d0c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialTailConvergence_exists_eventual_momentNormalized_moving_off_ball_exponential

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
    Tendsto
      (fun k : ℕ =>
        (∫ x : Space n in (Metric.ball x₀ r)ᶜ,
          monomialWeight (k : ℝ) (u k)
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
          monomialIntegral (k : ℝ) (u k)
            (momentNormalizedPotential F))
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨A, η, hA, hη, hbound⟩ :=
    exists_eventual_momentNormalized_moving_off_ball_exponential
      F htransport hu₀ hdu₀ x₀ hmax u hu hr
  have htop :
      Tendsto (fun k : ℕ => (k : ℝ) * (η / 2)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (half_pos hη)
  have hbot :
      Tendsto (fun k : ℕ => -((k : ℝ) * (η / 2)))
        atTop atBot := by
    simpa [Function.comp_def] using
      tendsto_neg_atTop_atBot.comp htop
  have hdecay :
      Tendsto
        (fun k : ℕ => Real.exp (-((k : ℝ) * (η / 2))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hbot
  have hmajor :
      Tendsto
        (fun k : ℕ => A * Real.exp (-((k : ℝ) * (η / 2))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hdecay.const_mul A
  apply squeeze_zero' _ hbound hmajor
  exact Filter.Eventually.of_forall fun k =>
    div_nonneg
      (setIntegral_nonneg Metric.isOpen_ball.measurableSet.compl
        fun x _ => (Real.exp_pos _).le)
      (by
        unfold monomialIntegral
        exact integral_nonneg fun x => (Real.exp_pos _).le)
end Ehrhart.BergmanJetMovingMonomialTailConvergence
