-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_truncation_integral_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:21:33.538652+00:00
-- url     : https://prove2.me/submissions/8f14acd4-97a9-405b-88d2-5d3a9847fb01

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_min_truncation_gap_le_quadratic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncated_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_integrable_of_integrable_real_square

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical

/-!
For a nonnegative random variable with finite quadratic moment,
the real expectation lost by clipping at R is between zero and C/R.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (R C : ℝ) (hR : 0 < R)
    (hYm : AEStronglyMeasurable Y P)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P ∧
      ∫ ω, (Y ω) ^ 2 ∂P ≤ C) :
    0 ≤ (∫ ω, Y ω ∂P) - (∫ ω, min (Y ω) R ∂P) ∧
      (∫ ω, Y ω ∂P) - (∫ ω, min (Y ω) R ∂P) ≤ C / R := by
  have hYi : Integrable Y P :=
    chat03_integrable_of_integrable_real_square Y hYm hY2.1
  have hMi : Integrable (fun ω => min (Y ω) R) P :=
    chat03_nonnegative_truncated_integrable Y R (le_of_lt hR) hYm hY0
  have hgi : Integrable (fun ω => Y ω - min (Y ω) R) P :=
    hYi.sub hMi
  have hqi : Integrable (fun ω => (Y ω) ^ 2 / R) P :=
    hY2.1.div_const R
  have hp : ∀ᵐ ω ∂P,
      0 ≤ Y ω - min (Y ω) R ∧
        Y ω - min (Y ω) R ≤ (Y ω) ^ 2 / R := by
    filter_upwards [hY0] with ω hy
    exact chat03_nonnegative_min_truncation_gap_le_quadratic R (Y ω) hR hy
  have hnonneg : 0 ≤ ∫ ω, Y ω - min (Y ω) R ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [hp] with ω hω
    exact hω.1
  have hle : (∫ ω, Y ω - min (Y ω) R ∂P) ≤
      ∫ ω, (Y ω) ^ 2 / R ∂P := by
    apply integral_mono_ae hgi hqi
    filter_upwards [hp] with ω hω
    exact hω.2
  have hbound : (∫ ω, (Y ω) ^ 2 / R ∂P) ≤ C / R := by
    rw [integral_div]
    exact div_le_div_of_nonneg_right hY2.2 (le_of_lt hR)
  rw [integral_sub hYi hMi] at hnonneg hle
  exact ⟨hnonneg, hle.trans hbound⟩
