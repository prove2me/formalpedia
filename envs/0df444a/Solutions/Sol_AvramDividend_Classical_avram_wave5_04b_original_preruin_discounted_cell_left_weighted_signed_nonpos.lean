-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:56:17.246433+00:00
-- url     : https://prove2.me/submissions/34b6e46f-3d58-40eb-9fdb-6538dd7235b6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The true complete Stieltjes discounted cell integral plus its source-frozen cap-linear signed correction, weighted at the left endpoint, is nonpositive at reserve zero and cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by
  have hMass := avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination
    X x c hc w V hw_cont hw_smooth hw_grad hV
    D hD ω a b hab hPre
  have hMassNonneg :
      0 ≤ (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal :=
    ENNReal.toReal_nonneg
  have hDropNonneg : 0 ≤
      V (x + X.X b ω - rightLimit D a ω) -
        V (x + X.X b ω - rightLimit D b ω) := by
    linarith only [hMass, hMassNonneg]
  have hWeighted :=
    avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
      X x c hc q hq w V hw_cont hw_smooth hw_grad hV
      D hD ω a b hab hPre
  have hExpNonneg : 0 ≤ Real.exp (-(q * (a : ℝ))) :=
    (Real.exp_pos _).le
  have hProductFinite :
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal (V (x + X.X b ω - rightLimit D a ω) -
        V (x + X.X b ω - rightLimit D b ω)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_mul hExpNonneg]
    simp
  have hReal := ENNReal.toReal_mono hProductFinite hWeighted
  rw [ENNReal.toReal_mul] at hReal
  rw [ENNReal.toReal_ofReal hExpNonneg,
      ENNReal.toReal_ofReal hDropNonneg] at hReal
  nlinarith only [hReal]
