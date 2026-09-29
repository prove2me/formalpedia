-- Prove2me | solution 1 for BanditAlgorithm.integral_discountedStoppedSum_sub_charge
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:06:31.503274+00:00
-- url     : https://prove2.me/submissions/1c831f4d-921b-4ed6-857f-50f336b91a2d

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Theorems.Thm_BanditAlgorithm_discountedStoppedSum_sub_charge
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum_one

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

private theorem measurable_abs_tsum'
    {S : Type*} [MeasurableSpace S] {α : ℝ} {r : S → ℝ}
    (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) := by
  apply Measurable.tsum
  intro t
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (by
      have : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
        hr.comp (measurable_pi_apply t)
      fun_prop))

private theorem ae_summable_abs'
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top (measurable_abs_tsum' hr) (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x) =
      (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) -
        γ * (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x) := by
  have hae : ∀ᵐ ω ∂markovChainMeasure P x,
      discountedStoppedSum α (fun y ↦ r y - γ) τ ω =
        discountedStoppedSum α r τ ω -
          γ * discountedStoppedSum α (fun _ : S ↦ 1) τ ω := by
    filter_upwards [ae_summable_abs' P hr hα0 hint x] with ω hω
    exact discountedStoppedSum_sub_charge hα0 hα1 r τ ω hω
  rw [integral_congr_ae hae]
  rw [integral_sub
    (integrable_discountedStoppedSum P hr hα0 hint x hτ)
    ((integrable_discountedStoppedSum_one P hα0 hα1 x hτ).const_mul γ)]
  rw [integral_const_mul]
