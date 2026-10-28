-- Prove2me | solution 1 for AvramDividend.Classical.bv_uniform_expected_monotone_count_ae_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:37:18.937693+00:00
-- url     : https://prove2.me/submissions/bd6c9fee-e5d9-496b-86d8-32e4f8c91cf5

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-- A monotone sequence of nonnegative random counts with bounded expectations has finite pointwise supremum a.e. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hF : ∀ n, Measurable (F n))
    (hMono : Monotone F)
    (hBound : ∀ n, (∫⁻ ω, F n ω ∂P) ≤ C)
    (hFinite : C < ⊤) :
    ∀ᵐ ω ∂P, (⨆ n, F n ω) < ⊤ := by
  have hInt : (∫⁻ ω, ⨆ n, F n ω ∂P) ≤ C := by
    rw [lintegral_iSup hF hMono]
    exact iSup_le hBound
  have hIntFinite : (∫⁻ ω, ⨆ n, F n ω ∂P) ≠ ∞ :=
    (lt_of_le_of_lt hInt hFinite).ne
  exact ae_lt_top (Measurable.iSup hF) hIntFinite
