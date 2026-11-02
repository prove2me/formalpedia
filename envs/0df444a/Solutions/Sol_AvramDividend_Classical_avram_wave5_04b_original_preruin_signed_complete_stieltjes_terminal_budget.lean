-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_signed_complete_stieltjes_terminal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:59:44.017368+00:00
-- url     : https://prove2.me/submissions/fed1a0f2-c002-4998-acb1-3f45bc60073f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_full_stieltjes_caplinear_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (hV : ∀ y : ℝ, V y = if y ≤ c then w y else w c + (y - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
        V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω) ≤ 0 := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω T hPre
  have hCover : rightLimit D T ω ≤ x + X.X T ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hStrategy.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hStrategy.1 ω] using hm
  have hRightNonneg : 0 ≤ rightLimit D T ω := le_trans hDnonneg
    (dividendStrategy_le_rightLimit D hStrategy ω T)
  have horder : x + X.X T ω - rightLimit D T ω ≤ x + X.X T ω := by
    linarith only [hRightNonneg]
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (x + X.X T ω - rightLimit D T ω) (x + X.X T ω)
    (sub_nonneg.mpr hCover) horder
  rw [←hV (x + X.X T ω),
      ←hV (x + X.X T ω - rightLimit D T ω)] at hsec
  have hdrop : 0 ≤ V (x + X.X T ω) -
      V (x + X.X T ω - rightLimit D T ω) := by
    linarith only [hsec, hRightNonneg]
  have hbound := avram_wave5_04b_original_preruin_full_stieltjes_caplinear_budget
    X x c hc q hq w hw_cont hw_smooth hw_grad D hD ω T hPre
  rw [←hV (x + X.X T ω),
      ←hV (x + X.X T ω - rightLimit D T ω)] at hbound
  have hreal := ENNReal.toReal_mono (by simp) hbound
  rw [ENNReal.toReal_ofReal hdrop] at hreal
  linarith only [hreal]
