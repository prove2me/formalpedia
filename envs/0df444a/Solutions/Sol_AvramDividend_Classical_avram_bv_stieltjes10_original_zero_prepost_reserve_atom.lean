-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_stieltjes10_original_zero_prepost_reserve_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:37:45.607303+00:00
-- url     : https://prove2.me/submissions/bb7c68d8-4dc6-488f-8868-9e79ea2e5ad0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The prepayment reserve at time zero differs from the grid's fallback
left limit by exactly the original right-dividend Stieltjes payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal
        (riskProcess X x D 0 ω -
          Function.leftLim
            (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) 0) := by
  calc
    dividendMeasure D ω {(0 : ℝ)}
        = ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
            simpa using
              (dividendMeasure_singleton_eq_rightLimit_sub D hD ω (0 : ℝ≥0))
    _ = ENNReal.ofReal
          (riskProcess X x D 0 ω -
            Function.leftLim
              (fun t : ℝ≥0 =>
                x + X.X t ω - rightLimit D t ω) 0) := by
            congr 1
            have hzero : IsBot (0 : ℝ≥0) := by
              simpa only [bot_eq_zero] using (isBot_bot : IsBot (⊥ : ℝ≥0))
            rw [leftLim_eq_of_isBot hzero]
            simp only [riskProcess, X.X_zero]
            ring
