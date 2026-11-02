-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_full_stieltjes_caplinear_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:44:54.956963+00:00
-- url     : https://prove2.me/submissions/6707999c-f831-4e12-8d40-c17b5b6f8ea3

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
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
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if x + X.X T ω ≤ c then w (x + X.X T ω)
        else w c + (x + X.X T ω - c)) -
      (if x + X.X T ω - rightLimit D T ω ≤ c
        then w (x + X.X T ω - rightLimit D T ω)
        else w c + ((x + X.X T ω - rightLimit D T ω) - c))) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω T hPre
  have hCover : rightLimit D T ω ≤ x + X.X T ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hStrategy.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hStrategy.1 ω] using hm
  have hLnonneg : 0 ≤ rightLimit D T ω := le_trans hDnonneg
    (dividendStrategy_le_rightLimit D hStrategy ω T)
  have hab : x + X.X T ω - rightLimit D T ω ≤ x + X.X T ω := by
    linarith
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (x + X.X T ω - rightLimit D T ω) (x + X.X T ω)
    (sub_nonneg.mpr hCover) hab
  have hdrop : rightLimit D T ω ≤
      (if x + X.X T ω ≤ c then w (x + X.X T ω)
        else w c + (x + X.X T ω - c)) -
      (if x + X.X T ω - rightLimit D T ω ≤ c
        then w (x + X.X T ω - rightLimit D T ω)
        else w c + ((x + X.X T ω - rightLimit D T ω) - c)) := by
    linarith only [hsec]
  have hsubset :
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) ⊆
        Icc (0 : ℝ) (T : ℝ) := by
    intro s hs
    exact ⟨hs.1.1, hs.2⟩
  calc
    _ ≤ (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω) :=
        lintegral_mono_set hsubset
    _ ≤ ENNReal.ofReal (rightLimit D T ω) :=
      avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
        q hq D hStrategy ω T
    _ ≤ _ := ENNReal.ofReal_le_ofReal hdrop
