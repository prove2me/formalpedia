-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_integrable_tight_error_and_vanishing_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:32:55.656207+00:00
-- url     : https://prove2.me/submissions/cac61a4c-d4ba-46be-a536-5c5d2f07cd27

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_tight_positive_excess_le_any_error

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An integrable payoff and baseline inherit the vanishing positive-error
    estimate from every pointwise dominating integrable error envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F G Err : ℕ → Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P)
    (hG : ∀ n, Integrable (G n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hlim : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ G n ω + max (Err n ω) 0) :
    (∀ n, Integrable (fun ω => max (F n ω - G n ω) 0) P) ∧
    Tendsto (fun n => ∫ ω, max (F n ω - G n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hInt : ∀ n, Integrable
      (fun ω => max (F n ω - G n ω) 0) P := by
    intro n
    exact ((hF n).sub (hG n)).pos_part
  have hUpper (n : ℕ) :
      (∫ ω, max (F n ω - G n ω) 0 ∂P) ≤
        (∫ ω, max (Err n ω) 0 ∂P) := by
    apply integral_mono_ae (hInt n) (hErr n)
    filter_upwards [hbudget n] with ω hω
    exact avram_a19_tight_positive_excess_le_any_error
      (F n ω) (G n ω) (Err n ω) hω
  have hLower (n : ℕ) :
      0 ≤ (∫ ω, max (F n ω - G n ω) 0 ∂P) :=
    integral_nonneg fun ω => le_max_right _ _
  exact ⟨hInt, squeeze_zero hLower hUpper hlim⟩
