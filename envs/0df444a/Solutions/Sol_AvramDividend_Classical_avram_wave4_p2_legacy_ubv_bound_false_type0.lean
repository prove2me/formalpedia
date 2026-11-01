-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_legacy_ubv_bound_false_type0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:37:06.255228+00:00
-- url     : https://prove2.me/submissions/6c240aa4-7988-407b-a1f7-7696e7a38854

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_ubv_core_false_type0

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
        (w : ℝ → ℝ) (C : ℝ≥0∞)
        (hw_cont : ContinuousOn w (Ici 0))
        (hw_neg : ∀ y < 0, w y = 0)
        (hw_smooth : ContDiffOn ℝ 2 w
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
        (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          1 ≤ deriv w y)
        (x : ℝ)
        (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
        (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 ≤ w (riskProcess X x D t ω))
        (T : ℝ) (hT : 0 ≤ T),
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) := by
  intro hall
  apply avram_wave3_04_canonical_ubv_core_false_type0
  intro Ω mΩ P 𝓕 X hX hBV q hq w C hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hw_nonneg hjump T hT
  exact hall X hX hBV q hq w C hw_cont hw_neg hw_smooth hw_gen hw_grad
    x D hD hw_nonneg T hT
