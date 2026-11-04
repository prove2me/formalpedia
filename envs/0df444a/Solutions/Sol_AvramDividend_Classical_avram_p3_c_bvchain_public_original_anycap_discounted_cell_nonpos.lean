-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:25:14.480518+00:00
-- url     : https://prove2.me/submissions/e81889f8-b272-4af5-bbc3-3df8a8a2355c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_discount_left_full_measure_le
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original complete discounted source-frozen dividend-cell sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hFinite :
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≠ ⊤ := by
    rw [dividendMeasure_Ioc_rightLimit D hStrategy ω a b]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hCash := avram_p3_c_bvchain_public_discount_left_full_measure_le
    q hq (dividendMeasure D ω) (a : ℝ) (b : ℝ)
  have hCashReal := ENNReal.toReal_mono hFinite hCash
  have hExpNonneg : 0 ≤ Real.exp (-(q * (a : ℝ))) :=
    (Real.exp_pos _).le
  have hCashScaled :
      (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ≤
      Real.exp (-(q * (a : ℝ))) *
        (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal := by
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hExpNonneg] using hCashReal
  have hDrop :=
    avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
      X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
        D hD ω a b hab hPre
  have hWeighted := mul_nonpos_of_nonneg_of_nonpos
    (Real.exp_pos (-(q * (a : ℝ)))).le hDrop
  nlinarith only [hCashScaled, hWeighted]
