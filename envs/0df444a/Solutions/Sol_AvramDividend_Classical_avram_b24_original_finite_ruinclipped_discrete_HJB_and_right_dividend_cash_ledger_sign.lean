-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T20:01:24.232209+00:00
-- url     : https://prove2.me/submissions/e2bbccf7-ed51-4a38-ba91-9cdb2794485e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_masked_discounted_strict_HJB_finite_physical_grid_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (y : ι → ℝ) (active : ι → Bool)
    (hTimes : ∀ i ∈ S, s i ≤ t i)
    (hInterior : ∀ i ∈ S, active i = true →
      0 < y i ∧ ENNReal.ofReal (y i) < C)
    (ω : Ω) (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i ∈ S, if active i then
      Real.exp (-(q * (s i : ℝ))) *
        ((t i : ℝ) - (s i : ℝ)) *
        (X.generator w (y i) - q * w (y i))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0 := by
  have hHJB :=
    AvramDividend.Classical.avram_b24_original_ruinclipped_masked_discounted_strict_HJB_finite_physical_grid_nonpositive
      X q hq w C hC hgen S s t y active hTimes hInterior
  have hPay :=
    AvramDividend.Classical.avram_b24_original_discounted_all_pre_ruin_right_dividend_payment_jump_corrections_nonpositive
      X x D q w hjump ω R hPre
  exact add_nonpos hHJB hPay
