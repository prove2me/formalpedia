-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_stochastic_localiser_fatou_no_extra_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:19:33.257163+00:00
-- url     : https://prove2.me/submissions/a33ef794-127c-4e6d-8079-0da99260f157

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_stopped_martingale_localiser_clocks
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_uniform_stopped_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSmono : ∀ ω, Monotone (fun n => S n ω))
    (hSsup : ∀ ω, (⨆ n, S n ω) = ⊤)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hnonneg :=
    avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
      X w C hw0 hw_cont hw_smooth hw_grad x D hD
  have hclocks :=
    avram_wave5_05_original_stopped_martingale_localiser_clocks
      X x D hD.1.1 S hSstop hSmono hSsup
  exact avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hnonneg hjump T hT
    (fun n ω => min (ruinTime X x D ω) (S n ω))
    hclocks.2.1 hclocks.2.2.1 hclocks.2.2.2 hBudget
