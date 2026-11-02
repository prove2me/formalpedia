-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_countable_horizon_exact_discounted_integral_domains
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:59:01.959206+00:00
-- url     : https://prove2.me/submissions/71477b46-920a-4f64-b82c-aec111e39a7a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! One probability-one event gives exact source dividend integral
    domains eventually at every countable finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (horizons : ℕ → ℝ)
    (hT : ∀ k : ℕ, 0 ≤ horizons k) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (S n ω)) ∩ Iic (horizons k),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (horizons k),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have hdom :=
    avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises
      X hBV x C D hD S hSliminfAE horizons hT
  filter_upwards [hdom] with ω hω
  intro k
  rcases hω k with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [hN n hn]
end
