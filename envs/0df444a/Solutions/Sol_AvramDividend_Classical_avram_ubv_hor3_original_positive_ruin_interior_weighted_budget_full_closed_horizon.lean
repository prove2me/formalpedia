-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_interior_weighted_budget_full_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:32:29.413203+00:00
-- url     : https://prove2.me/submissions/790cd952-324f-4ee6-97a4-472688bfe5e6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_ruin_weighted_budget_glues_closed_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (T : ℝ) (hT : 0 < T)
    (hInterior :
      (∫⁻ ω in {ω : Ω | ruinTime X x D ω ≠ 0},
        (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
        ENNReal.ofReal (w x) * P {ω : Ω | ruinTime X x D ω ≠ 0}) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hDS : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hDS
  have hEvent : MeasurableSet {ω : Ω | ruinTime X x D ω = 0} := by
    exact
      (measurableSet_singleton (0 : ℝ≥0∞)).preimage hRuinMeas
  exact avram_ubv_hor3_original_positive_ruin_weighted_budget_glues_closed_horizon
    X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc D hD hjump n hn T hT
    (fun ω => ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
    (fun _ => rfl) hEvent hInterior
