-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:54:46.951047+00:00
-- url     : https://prove2.me/submissions/d39c6879-6317-4f82-ad69-9fe70dffd848

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Correct BV terminal sign at every actual post-payment reserve and at initial time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (x + X.X t ω - rightLimit D t ω) := by
  let y : ℝ := x + X.X t ω - rightLimit D t ω
  change 0 ≤ w y
  have hcap : ENNReal.ofReal y ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  by_cases hy : 0 ≤ y
  · have hs : y - 0 ≤ w y - w 0 :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad 0 y
        (le_refl (0 : ℝ)) hy hcap
    linarith
  · have hneg : y < 0 := lt_of_not_ge hy
    simp [hw_neg y hneg]
