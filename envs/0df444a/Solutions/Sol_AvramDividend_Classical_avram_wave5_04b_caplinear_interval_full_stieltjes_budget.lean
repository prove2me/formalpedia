-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_caplinear_interval_full_stieltjes_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:54:21.344652+00:00
-- url     : https://prove2.me/submissions/4bdb32c5-0e87-46db-9cc5-740357c06bc8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (y : ℝ)
    (hy : rightLimit D b ω ≤ y) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if y - rightLimit D a ω ≤ c
        then w (y - rightLimit D a ω)
        else w c + ((y - rightLimit D a ω) - c)) -
      (if y - rightLimit D b ω ≤ c
        then w (y - rightLimit D b ω)
        else w c + ((y - rightLimit D b ω) - c))) := by
  have hmono : rightLimit D a ω ≤ rightLimit D b ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω) hab
  have hpost : 0 ≤ y - rightLimit D b ω := sub_nonneg.mpr hy
  have horder : y - rightLimit D b ω ≤ y - rightLimit D a ω := by
    linarith only [hmono]
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (y - rightLimit D b ω) (y - rightLimit D a ω) hpost horder
  have hdrop : rightLimit D b ω - rightLimit D a ω ≤
      (if y - rightLimit D a ω ≤ c
        then w (y - rightLimit D a ω)
        else w c + ((y - rightLimit D a ω) - c)) -
      (if y - rightLimit D b ω ≤ c
        then w (y - rightLimit D b ω)
        else w c + ((y - rightLimit D b ω) - c)) := by
    linarith only [hsec]
  have hnonneg : ∀ s : ℝ, s ∈ Ioc (a : ℝ) (b : ℝ) → 0 ≤ s := by
    intro s hs
    exact le_trans (show (0 : ℝ) ≤ (a : ℝ) from a.property) hs.1.le
  calc
    _ ≤ dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) :=
      discounted_stieltjes_lintegral_le_measure q hq
        (dividendMeasure D ω) (Ioc (a : ℝ) (b : ℝ))
        measurableSet_Ioc hnonneg
    _ = ENNReal.ofReal (rightLimit D b ω - rightLimit D a ω) :=
      dividendMeasure_Ioc_rightLimit D hD ω a b
    _ ≤ _ := ENNReal.ofReal_le_ofReal hdrop
