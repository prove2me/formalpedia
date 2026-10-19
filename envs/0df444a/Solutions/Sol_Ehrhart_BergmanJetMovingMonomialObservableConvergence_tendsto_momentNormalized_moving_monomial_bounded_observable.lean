-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialObservableConvergence.tendsto_momentNormalized_moving_monomial_bounded_observable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/9df18845-6120-4224-a7d7-802467661b49

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialTailConvergence_tendsto_momentNormalized_moving_off_ball_probability
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialObservableConvergence_tendsto_integral_bounded_continuous_of_concentrating_normalized_density

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingMonomialObservableConvergence
open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetMovingMonomialTailConvergence
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingMonomialObservableConvergence
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
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        (∫ x : Space n,
          f x * monomialWeight (k : ℝ) (u k)
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) /
          monomialIntegral (k : ℝ) (u k)
            (momentNormalizedPotential F))
      atTop (𝓝 (f x₀)) := by
  let φ : Space n → ℝ := momentNormalizedPotential F
  let w : ℕ → Space n → ℝ := fun k x =>
    monomialWeight (k : ℝ) (u k) φ x /
      monomialIntegral (k : ℝ) (u k) φ
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  have hwint :
      ∀ᶠ k : ℕ in atTop,
        Integrable (w k) (volume : Measure (Space n)) := by
    filter_upwards [hinterior, eventually_ge_atTop (1 : ℕ)]
      with k hkint hkone
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkone)
    exact
      (integrable_monomialWeight_momentNormalized_of_mem_interior
        F htransport hkint hkpos).div_const _
  have hwnonneg : ∀ k : ℕ, ∀ x : Space n, 0 ≤ w k x := by
    intro k x
    dsimp [w]
    apply div_nonneg (Real.exp_pos _).le
    unfold monomialIntegral
    exact integral_nonneg fun y => (Real.exp_pos _).le
  have hwmass :
      ∀ᶠ k : ℕ in atTop,
        (∫ x : Space n, w k x
          ∂(volume : Measure (Space n))) = 1 := by
    filter_upwards [hinterior, eventually_ge_atTop (1 : ℕ)]
      with k hkint hkone
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkone)
    dsimp [w]
    rw [MeasureTheory.integral_div]
    exact div_self
      (monomialIntegral_momentNormalized_pos
        F htransport hkint hkpos).ne'
  have hwtail : ∀ {r : ℝ}, 0 < r →
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n in (Metric.ball x₀ r)ᶜ,
            w k x ∂(volume : Measure (Space n)))
        atTop (𝓝 (0 : ℝ)) := by
    intro r hr
    have ht := tendsto_momentNormalized_moving_off_ball_probability
      F htransport hu₀ hdu₀ x₀ hmax u hu hr
    simpa [w, φ, MeasureTheory.integral_div] using ht
  have ht :=
    tendsto_integral_bounded_continuous_of_concentrating_normalized_density
      w hwint hwnonneg hwmass x₀ hwtail f hf C hC
  simpa [w, φ, ← mul_div_assoc, MeasureTheory.integral_div] using ht
end Ehrhart.BergmanJetMovingMonomialObservableConvergence
