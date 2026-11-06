-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_ae_cofinal_discounted_full_payoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:09:47.31978+00:00
-- url     : https://prove2.me/submissions/2d43f06f-ae03-4c0b-a83c-b0e9ebcb9151

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :
    let Reward : ℝ≥0 → Ω → ℝ := fun t ω =>
      Real.exp (-(q * (t : ℝ))) *
        w (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X t ω - rightLimit D t ω
          else riskProcess X x D t ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    ∀ᵐ ω ∂P, Tendsto
      (fun k => ENNReal.ofReal (Reward (τk k ω) ω)) atTop
      (𝓝 (ENNReal.ofReal (Reward (τ ω) ω))) := by
  let Reward : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(q * (t : ℝ))) *
      w (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X t ω - rightLimit D t ω
        else riskProcess X x D t ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  change ∀ᵐ ω ∂P, Tendsto
    (fun k => ENNReal.ofReal (Reward (τk k ω) ω)) atTop
    (𝓝 (ENNReal.ofReal (Reward (τ ω) ω)))
  have hClock :=
    avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq
      X x D n S hSmono hSsup τ hτ τk hτk
  filter_upwards [hClock] with ω hω
  obtain ⟨N, hN⟩ := hω
  have hEq :
      (fun k => ENNReal.ofReal (Reward (τk k ω) ω))
        =ᶠ[atTop]
      (fun _ : ℕ => ENNReal.ofReal (Reward (τ ω) ω)) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    simp only [hN k hk]
  exact (tendsto_congr' hEq).2 tendsto_const_nhds
