-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:42:10.718204+00:00
-- url     : https://prove2.me/submissions/2c29cffa-c496-4a71-b310-16f57898a646

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine source-specific discounted Stieltjes cell is charged at its left-time weight against the source-frozen cap-linear value drop; endpoints may be zero or the cap. -/
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
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal (V (x + X.X b ω - rightLimit D a ω) -
          V (x + X.X b ω - rightLimit D b ω)) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω b hPre
  have hCover : rightLimit D b ω ≤ x + X.X b ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hmono : rightLimit D a ω ≤ rightLimit D b ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone D hStrategy ω) hab
  have hpost : 0 ≤ (x + X.X b ω) - rightLimit D b ω := sub_nonneg.mpr hCover
  have horder :
      (x + X.X b ω) - rightLimit D b ω ≤
        (x + X.X b ω) - rightLimit D a ω := by
    linarith only [hmono]
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    ((x + X.X b ω) - rightLimit D b ω)
    ((x + X.X b ω) - rightLimit D a ω) hpost horder
  have hdrop : rightLimit D b ω - rightLimit D a ω ≤
      V (x + X.X b ω - rightLimit D a ω) -
        V (x + X.X b ω - rightLimit D b ω) := by
    rw [hV (x + X.X b ω - rightLimit D a ω),
      hV (x + X.X b ω - rightLimit D b ω)]
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
