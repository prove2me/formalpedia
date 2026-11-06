-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:40:48.783064+00:00
-- url     : https://prove2.me/submissions/d169c62a-0ffc-4007-b07a-2dc6c6faa0cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_hjb_discounted_generator_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_discounted_slope_defect_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual source HJB generator and continuous dividend-rate control have joint nonpositive drift. -/
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
    (r : ℝ≥0 × Ω → ℝ) (hr : ∀ p, 0 ≤ r p) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    ∀ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        ((X.generator w (U p) - q * w (U p)) +
          r p * (1 - deriv w (U p))) ≤ 0 := by
  dsimp only
  intro p
  have hG :=
    (avram_p4_f3_original_clipped_hjb_discounted_generator_nonpos
      X x D w C q hw_gen δ K hδ hδK hK) p
  have hSlope :=
    (avram_p4_f3_original_clipped_discounted_slope_defect_nonpos
      X x D w C q hw_grad δ K hδ hδK hK) p
  have hRate :
      Real.exp (-(q * (p.1 : ℝ))) *
        (r p * (1 - deriv w
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
           if y ∈ Icc δ K then y else δ))) ≤ 0 := by
    calc
      _ = r p * (Real.exp (-(q * (p.1 : ℝ))) *
          (1 - deriv w
            (let y := Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
             if y ∈ Icc δ K then y else δ))) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hr p) hSlope
  calc
    _ = Real.exp (-(q * (p.1 : ℝ))) *
          (X.generator w
            (let y := Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
             if y ∈ Icc δ K then y else δ) -
           q * w
            (let y := Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
             if y ∈ Icc δ K then y else δ)) +
        Real.exp (-(q * (p.1 : ℝ))) *
          (r p * (1 - deriv w
            (let y := Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
             if y ∈ Icc δ K then y else δ))) := by ring
    _ ≤ 0 := add_nonpos hG hRate
