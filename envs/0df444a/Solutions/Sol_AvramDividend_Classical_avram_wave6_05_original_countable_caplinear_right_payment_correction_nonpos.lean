-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_original_countable_caplinear_right_payment_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:49:01.830548+00:00
-- url     : https://prove2.me/submissions/9f47df74-ac50-439c-bd6e-b4c1c04278bf

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- All countably many actual right-payment corrections are nonpositive,
including the initial atom and original simultaneous source jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (A : Set ℝ≥0) (hCount : A.Countable)
    (hA : ∀ t : A,
      (t : ℝ≥0) = 0 ∨
        ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : A => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        V (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        V (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        V (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        V (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by
  have hJump :
      ∀ t : ℝ≥0,
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
          rightLimit D t ω - D t ω ≤
            V (riskProcess X x D t ω) -
              V (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω)) := by
    intro t ht
    exact avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
      X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω t ht
  exact avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos
    X x D V ω q hJump A hCount hA hSummable
