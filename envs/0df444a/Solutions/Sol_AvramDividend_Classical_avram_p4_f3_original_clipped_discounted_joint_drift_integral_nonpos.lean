-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_joint_drift_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:50:01.707973+00:00
-- url     : https://prove2.me/submissions/9dde7138-3054-4a10-970b-b29fdadd7b7b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original clipped path generator plus dividend-control drift has nonpositive joint integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (r : ℝ≥0 × Ω → ℝ) (hr : ∀ p, 0 ≤ r p)
    (μ : Measure (ℝ≥0 × Ω)) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
      if y ∈ Icc δ K then y else δ
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((X.generator w (U p) - q * w (U p)) +
          r p * (1 - deriv w (U p)))
    Integrable H μ → (∫ p, H p ∂μ) ≤ 0 := by
  dsimp only
  intro hL1
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [] with p
  exact
    (avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
      X x D w C q hw_gen hw_grad δ K hδ hδK hK r hr) p
