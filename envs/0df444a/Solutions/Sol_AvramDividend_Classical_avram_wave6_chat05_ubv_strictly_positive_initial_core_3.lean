-- Prove2me | solution 3 for AvramDividend.Classical.avram_wave6_chat05_ubv_strictly_positive_initial_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:02:46.491127+00:00
-- url     : https://prove2.me/submissions/06cbef40-15a1-461e-9f13-4b90d0bdb8ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_random_closed_clock_expected_cash_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hTpos : 0 < max T 1 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right T 1)
  let τ : Ω → ℝ≥0 := fun _ => ⟨T, hT⟩
  let σ : Ω → ℝ≥0 := fun _ => ⟨max T 1, le_of_lt hTpos⟩
  have hτσ : ∀ ω, τ ω ≤ σ ω := by
    intro ω
    change T ≤ max T 1
    exact le_max_left T 1
  have hτeval (ω : Ω) : (τ ω : ℝ) = T := by
    change ((⟨T, hT⟩ : ℝ≥0) : ℝ) = T
    exact NNReal.coe_mk T hT
  have hσeval (ω : Ω) : (σ ω : ℝ) = max T 1 := by
    change ((⟨max T 1, le_of_lt hTpos⟩ : ℝ≥0) : ℝ) = max T 1
    exact NNReal.coe_mk (max T 1) (le_of_lt hTpos)
  have hMonotone :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (max T 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
    simpa only [hτeval, hσeval] using
      (avram_wave6_chat09_original_random_closed_clock_expected_cash_monotone
        X x D q τ σ hτσ)
  exact hMonotone.trans
    (avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump (max T 1) hTpos)
