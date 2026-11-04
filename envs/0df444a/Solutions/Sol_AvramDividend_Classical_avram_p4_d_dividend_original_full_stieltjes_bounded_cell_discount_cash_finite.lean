-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_bounded_cell_discount_cash_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:07:52.78633+00:00
-- url     : https://prove2.me/submissions/c29959db-af7a-4e05-b5fb-23a55c7464a2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original bounded-horizon full Stieltjes cash is finite on every contained payment cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b T : ℝ≥0) (hbT : b ≤ T) :
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) < ⊤ := by
  have hsubset : Ioc (a : ℝ) (b : ℝ) ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    constructor
    · have ha : 0 ≤ (a : ℝ) := NNReal.coe_nonneg _
      linarith [hu.1]
    · have hT : (b : ℝ) ≤ (T : ℝ) := by exact_mod_cast hbT
      exact le_trans hu.2 hT
  have hmass : dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) < ⊤ := by
    calc
      dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
          dividendMeasure D ω (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  have ha : 0 ≤ (a : ℝ) := NNReal.coe_nonneg _
  have hfactor : ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) ≤ 1 := by
    calc
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) ≤ ENNReal.ofReal 1 := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_nonneg hq ha]
      _ = 1 := by norm_num
  have hUpper :=
    (avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich
      D hD ω q hq a b).2
  calc
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
          dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := hUpper
    _ ≤ 1 * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor zero_le
    _ = dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := one_mul _
    _ < ⊤ := hmass
