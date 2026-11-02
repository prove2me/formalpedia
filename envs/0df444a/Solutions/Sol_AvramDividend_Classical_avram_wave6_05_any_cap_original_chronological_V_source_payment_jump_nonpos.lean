-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_any_cap_original_chronological_V_source_payment_jump_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:24:43.945047+00:00
-- url     : https://prove2.me/submissions/d24daa37-75bc-4756-8599-d0039cc4c06e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_chronological_ito_jump_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Split the simultaneous original source jump and right dividend atom at any
cap; the full cash-plus-V dividend residual is nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (w V : ℝ → ℝ)
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
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    let before : ℝ :=
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω
    let afterSource : ℝ := x + X.X t ω - D t ω
    let afterPayment : ℝ := x + X.X t ω - rightLimit D t ω
    let sourceJump : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let paymentAtom : ℝ := rightLimit D t ω - D t ω
    (V afterPayment - V before -
        deriv V before * (sourceJump - paymentAtom) =
      (V afterSource - V before - deriv V before * sourceJump) +
        (V afterPayment - V afterSource + deriv V before * paymentAtom)) ∧
      V afterPayment - V afterSource + paymentAtom ≤ 0 := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hDrop :
      rightLimit D t ω - D t ω ≤
        V (riskProcess X x D t ω) -
          V (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
    by_cases hCzero : C = 0
    · have hDzero : IsAdmissibleLe X x (0 : ℝ≥0∞) D := by
        simpa only [hCzero] using hD
      have hVzero : ∀ y : ℝ,
          V y = if y ≤ 0 then w y else w 0 + y := by
        intro y
        have hForm := hVfinite (by simp [hCzero]) y
        simpa only [hCzero, ENNReal.toReal_zero, sub_zero] using hForm
      have hEq := avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact
        X x w V hVzero D hDzero ω t (Or.inr hPre)
      exact le_of_eq hEq
    · have hCpos : 0 < C := pos_iff_ne_zero.mpr hCzero
      exact avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
        X x C hCpos w V hw_cont hw_smooth hw_grad hVtop hVfinite
        D hD ω t (Or.inr hPre)
  have hPay :
      (x + X.X t ω - D t ω) -
        (rightLimit D t ω - D t ω) =
      x + X.X t ω - rightLimit D t ω := by
    ring
  have hJump :
      rightLimit D t ω - D t ω ≤
        V (x + X.X t ω - D t ω) -
          V (x + X.X t ω - rightLimit D t ω) := by
    simpa only [riskProcess, hPay] using hDrop
  exact avram_wave4_04b_chronological_ito_jump_correction
    X x D hStrategy V ω t ht hJump
