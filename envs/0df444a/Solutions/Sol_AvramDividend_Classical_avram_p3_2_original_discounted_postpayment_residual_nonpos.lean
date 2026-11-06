-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_discounted_postpayment_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:15:41.394509+00:00
-- url     : https://prove2.me/submissions/092a7d4b-40de-477d-93db-73a5b58667ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At a genuine positive original pre-ruin time, discounted post-Lévy
dividend payment contributes a nonpositive term to the stopped C1 budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω) +
          (rightLimit D t ω - D t ω)) ≤ 0 := by
  have hChron :=
    avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos
      X x C hC w hw_cont hw_smooth hw_grad D hD ω t ht hPre
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hChron.2
