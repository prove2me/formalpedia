-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_postpayment_terminal_nonnegative_weak_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:07:24.753996+00:00
-- url     : https://prove2.me/submissions/7c28a81e-01a6-478c-9672-50cf02211240

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (x + X.X t ω - rightLimit D t ω) := by
  by_cases hy : x + X.X t ω - rightLimit D t ω < 0
  · simpa [hw_neg _ hy]
  · have hy0 : 0 ≤ x + X.X t ω - rightLimit D t ω := le_of_not_gt hy
    have hyC := capped_postPaymentReserve_ofReal_le_cap
      X x C D hD hxc ω t
    have hyw := avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
      C w hw0 hw_cont hw_smooth hw_grad
      (x + X.X t ω - rightLimit D t ω) hy0 hyC
    exact le_trans hy0 hyw
