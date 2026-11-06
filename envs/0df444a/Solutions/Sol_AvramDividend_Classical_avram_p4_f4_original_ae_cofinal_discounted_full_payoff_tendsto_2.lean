-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f4_original_ae_cofinal_discounted_full_payoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:11:15.619821+00:00
-- url     : https://prove2.me/submissions/1c23b6ae-ed0a-41c1-99ba-d78df6babbbd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original discounted ruin-stopped payoff stabilises eventually
off the spatial-localiser exceptional set, preserving every cash endpoint. -/
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
  intro Reward
  have hClock :=
    avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq
      X x D n S hSmono hSsup τ hτ τk hτk
  filter_upwards [hClock] with ω hω
  obtain ⟨K, hK⟩ := hω
  have he : (fun k => ENNReal.ofReal (Reward (τk k ω) ω))
      =ᶠ[atTop] (fun _ => ENNReal.ofReal (Reward (τ ω) ω)) := by
    filter_upwards [eventually_ge_atTop K] with k hk
    rw [hK k hk]
  exact (tendsto_congr' he).2 tendsto_const_nhds
