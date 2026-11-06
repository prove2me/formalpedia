-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_postpayment_source_cash_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:21:55.814137+00:00
-- url     : https://prove2.me/submissions/03d93d27-212e-4db7-88b7-7f7ea546e338

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine original positive-time post-Lévy dividend cash corrections
sum to a nonpositive discounted contribution on each finite jump grid. -/
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
    (ω : Ω) (q : ℝ) (T : Finset ℝ≥0)
    (hT : ∀ t ∈ T, 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ T, Real.exp (-(q * (t : ℝ))) *
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω) +
          (rightLimit D t ω - D t ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro t ht
  have hTime := hT t ht
  have hChron :=
    avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos
      X x C hC w hw_cont hw_smooth hw_grad
      D hD ω t hTime.1 hTime.2
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hChron.2
