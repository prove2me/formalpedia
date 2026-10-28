-- Prove2me | solution 1 for AvramDividend.Classical.chat12_expected_record_sum_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:31:54.025266+00:00
-- url     : https://prove2.me/submissions/5a2f05f9-4eea-4a65-b851-a7eb53fb4e8b

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, Measurable (w n))
    (hbound : (∑' n : ℕ, ∫⁻ ω, w n ω ∂P) < ∞) :
    ∀ᵐ ω ∂P, (∑' n : ℕ, w n ω) < ∞ := by
  have hMeas : Measurable (fun ω => ∑' n : ℕ, w n ω) :=
    Measurable.ennreal_tsum hw
  have hEqual :
      (∫⁻ ω, ∑' n : ℕ, w n ω ∂P) =
        (∑' n : ℕ, ∫⁻ ω, w n ω ∂P) :=
    lintegral_tsum (fun n => (hw n).aemeasurable)
  apply ae_lt_top hMeas
  rw [hEqual]
  exact ne_of_lt hbound
