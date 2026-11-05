-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_initial_right_cash_le_candidate_even_immediate_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:43:34.458556+00:00
-- url     : https://prove2.me/submissions/8ba3df85-1643-40ce-89ee-813c8ca99ec6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original time-zero payout is bounded by the C1 verification candidate,
even if the first ruin clock vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ω : Ω) : rightLimit D 0 ω ≤ w x := by
  have hpost := avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
    X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD ω 0
  have hledger := avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
    X w x C D hD hjump ω
  have hnonneg : 0 ≤ w (x - rightLimit D 0 ω) := by
    simpa only [X.X_zero, add_zero] using hpost
  linarith only [hledger, hnonneg]
