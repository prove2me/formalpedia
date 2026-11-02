-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_zero_cap_original_any_index_discounted_right_payment_residual_tsum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:27:00.191702+00:00
-- url     : https://prove2.me/submissions/b734c396-f1ed-4463-a7d2-720b445e29b0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- At cap zero every actual dividend jump compensates its cash exactly,
so even an arbitrarily indexed discounted residual tsum vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (w V : ℝ → ℝ)
    (hVzero : ∀ y : ℝ,
      V y = if y ≤ 0 then w y else w 0 + y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (0 : ℝ≥0∞) D)
    (ω : Ω) (A : Set ℝ≥0)
    (hA : ∀ t : A, (t : ℝ≥0) = 0 ∨
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        V (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        V (riskProcess X x D (t : ℝ≥0) ω))) = 0 := by
  have hTerm : ∀ t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        V (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        V (riskProcess X x D (t : ℝ≥0) ω)) = 0 := by
    intro t
    have hEq := avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact
      X x w V hVzero D hD ω (t : ℝ≥0) (hA t)
    have hResidual :
        (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          V (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          V (riskProcess X x D (t : ℝ≥0) ω) = 0 := by
      linarith only [hEq]
    rw [hResidual]
    ring
  simp [hTerm]
