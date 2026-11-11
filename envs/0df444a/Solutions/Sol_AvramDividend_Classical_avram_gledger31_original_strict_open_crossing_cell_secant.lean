-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger31_original_strict_open_crossing_cell_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:14:39.027724+00:00
-- url     : https://prove2.me/submissions/c29b3c56-8bd4-4f14-9ba3-df869b2ce632

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger29_topcap_secant_without_contdiff
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_open_interval_dividend_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A stopped physical crossing cell uses the prepayment dividend
    increment, excluding the terminal right-payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (A : ℝ) (hpre : 0 ≤ A - D b ω)
    (hinc : 0 ≤ D b ω - rightLimit D a ω) :
    dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) ≤
      ENNReal.ofReal (w (A - rightLimit D a ω) - w (A - D b ω)) := by
  have hle : A - D b ω ≤ A - rightLimit D a ω := by linarith
  have hsec := avram_gledger29_topcap_secant_without_contdiff
    w hw_cont hw_grad (A - D b ω) (A - rightLimit D a ω) hpre hle
  have hdrop : D b ω - rightLimit D a ω ≤
      w (A - rightLimit D a ω) - w (A - D b ω) := by linarith
  rw [avram_p3_c_bvchain_original_open_interval_dividend_mass D hD ω a b]
  exact ENNReal.ofReal_le_ofReal hdrop
