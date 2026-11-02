-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_eventual_exact_discounted_stieltjes_integral_domains
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:56:23.820145+00:00
-- url     : https://prove2.me/submissions/65b7ad38-a535-497a-a94b-e74ccf10a782

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Pure domain extensionality for the original full dividend measure.
    This makes no new claim about stochastic Stieltjes integration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (T : ℝ) (hT : 0 ≤ T)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have hdom :=
    avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises
      X hBV x C D hD T hT S hSliminfAE
  filter_upwards [hdom] with ω hω
  rcases hω with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [hN n hn]
end
