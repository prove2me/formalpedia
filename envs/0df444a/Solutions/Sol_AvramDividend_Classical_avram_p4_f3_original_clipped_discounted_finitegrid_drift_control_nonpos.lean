-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_finitegrid_drift_control_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:49:53.531408+00:00
-- url     : https://prove2.me/submissions/c33a5c88-56ef-4434-8eb7-a31928faa981

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

/-- Discounted true-reserve clipped HJB drift/control has nonpositive total physical-grid budget. -/
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
    {ι : Type*} (s : Finset ι) (p : ι → ℝ≥0 × Ω)
    (Δ : ι → ℝ) (hΔ : ∀ i ∈ s, 0 ≤ Δ i) :
    let U : ℝ≥0 × Ω → ℝ := fun z =>
      let y := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t z.2 - rightLimit D t z.2) z.1
      if y ∈ Icc δ K then y else δ
    ∑ i ∈ s, Δ i *
      (Real.exp (-(q * ((p i).1 : ℝ))) *
        ((X.generator w (U (p i)) - q * w (U (p i))) +
          r (p i) * (1 - deriv w (U (p i))))) ≤ 0 := by
  dsimp only
  apply Finset.sum_nonpos
  intro i hi
  have hSource :=
    (avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
      X x D w C q hw_gen hw_grad δ K hδ hδK hK r hr) (p i)
  exact mul_nonpos_of_nonneg_of_nonpos (hΔ i hi) hSource
