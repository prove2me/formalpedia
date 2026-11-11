-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger34_original_strict_discounted_crossing_prepayment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:47:55.770478+00:00
-- url     : https://prove2.me/submissions/85a8ee84-8d6c-4f2c-a69e-3eb1dc0c6213

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger31_original_strict_open_crossing_cell_secant
import Theorems.Thm_AvramDividend_Classical_avram_gledger33_strict_discounted_open_cell_upper_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The strict crossing-cell cash excludes the final right-payment atom;
    discount and the prepayment secant are applied to the same Ioo mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (A : ℝ) (hpre : 0 ≤ A - D b ω)
    (hinc : 0 ≤ D b ω - rightLimit D a ω) :
    (∫⁻ s in Ioo (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (w (A - rightLimit D a ω) - w (A - D b ω)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) := by
  have hReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hR : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr hReal
  have hqd : 0 ≤ q * ((b : ℝ) - (a : ℝ)) := mul_nonneg hq hR
  have hE : 0 ≤ Real.exp (-(q * (b : ℝ))) := (Real.exp_pos _).le
  have hMass := avram_gledger31_original_strict_open_crossing_cell_secant
    D hD ω a b hab w hw_cont hw_grad A hpre hinc
  have hInterval : (0 : ℝ) ≤ (a : ℝ) := a.property
  have hBudget := avram_gledger33_strict_discounted_open_cell_upper_error
    q hq (dividendMeasure D ω) (a : ℝ) (b : ℝ) hInterval hReal
  calc
    (∫⁻ s in Ioo (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal
          (Real.exp (-(q * (b : ℝ))) + q * ((b : ℝ) - (a : ℝ))) *
          dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) := hBudget
    _ = ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) +
        ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
          dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) := by
      rw [ENNReal.ofReal_add hE hqd, add_mul]
    _ ≤ _ := by
      gcongr <;> exact hMass
