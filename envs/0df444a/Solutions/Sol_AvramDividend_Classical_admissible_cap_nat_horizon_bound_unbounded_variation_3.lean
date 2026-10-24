-- Prove2me | solution 3 for AvramDividend.Classical.admissible_cap_nat_horizon_bound_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:35:02.793009+00:00
-- url     : https://prove2.me/submissions/31587045-ffec-4583-9853-1cbd64987b85
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finite integer-horizon rewards are bounded by the corresponding closed
    real-horizon reward. The zero-horizon atom remains in both domains. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ) := by
    simpa only [ENNReal.ofReal_natCast] using
      (AvramDividend.Classical.paymentTimes_min_ofReal_subset_inter_horizon
        (ruinTime X x D ω) (n : ℝ) hn)
  have hinner (ω : Ω) :
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    lintegral_mono_set (hs ω)
  calc
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := lintegral_mono hinner
    _ ≤ ENNReal.ofReal (w x) :=
      AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb
        x hx hxc D hD (n : ℝ) hn
