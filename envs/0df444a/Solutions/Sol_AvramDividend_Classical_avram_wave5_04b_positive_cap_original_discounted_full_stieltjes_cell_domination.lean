-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:42:53.830149+00:00
-- url     : https://prove2.me/submissions/d1cc591b-d7b7-48e1-bc58-93b5f9265020

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Uniform finite-or-infinite positive-cap control of the actual source-specific discounted Stieltjes dividend cell, with all zero/cap contacts and singular-continuous dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal
          (V (x + X.X b ω - rightLimit D a ω) -
            V (x + X.X b ω - rightLimit D b ω)) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω b hPre
  have hCover : rightLimit D b ω ≤ x + X.X b ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hmono : rightLimit D a ω ≤ rightLimit D b ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone D hStrategy ω) hab
  have hpost : 0 ≤ x + X.X b ω - rightLimit D b ω := sub_nonneg.mpr hCover
  have horder :
      x + X.X b ω - rightLimit D b ω ≤
        x + X.X b ω - rightLimit D a ω := by
    linarith only [hmono]
  have hsec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    (x + X.X b ω - rightLimit D b ω)
    (x + X.X b ω - rightLimit D a ω) hpost horder
  have hdrop : rightLimit D b ω - rightLimit D a ω ≤
      V (x + X.X b ω - rightLimit D a ω) -
        V (x + X.X b ω - rightLimit D b ω) := by
    linarith only [hsec]
  calc
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
          dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) :=
      avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
        q hq (dividendMeasure D ω) (a : ℝ) (b : ℝ)
    _ = ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
          ENNReal.ofReal (rightLimit D b ω - rightLimit D a ω) := by
      rw [dividendMeasure_Ioc_rightLimit D hStrategy ω a b]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal hdrop) bot_le
