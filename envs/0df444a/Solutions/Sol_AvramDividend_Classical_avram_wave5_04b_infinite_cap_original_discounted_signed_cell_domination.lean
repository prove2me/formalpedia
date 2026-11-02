-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_infinite_cap_original_discounted_signed_cell_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:42:48.817904+00:00
-- url     : https://prove2.me/submissions/458ac232-d921-40ee-8cc5-9065294825fc

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_gradient_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual original-source discounted Stieltjes cell is bounded by the left-weighted true value drop at cap infinity, including reserve zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z})
    (hw_grad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal
          (w (x + X.X b ω - rightLimit D a ω) -
            w (x + X.X b ω - rightLimit D b ω)) := by
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
  have hsec := avram_wave5_04b_infinite_cap_gradient_global_secant
    w hw_cont hw_smooth hw_grad
    ((x + X.X b ω) - rightLimit D b ω)
    ((x + X.X b ω) - rightLimit D a ω) hpost horder
  have hdrop : rightLimit D b ω - rightLimit D a ω ≤
      w (x + X.X b ω - rightLimit D a ω) -
        w (x + X.X b ω - rightLimit D b ω) := by
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
