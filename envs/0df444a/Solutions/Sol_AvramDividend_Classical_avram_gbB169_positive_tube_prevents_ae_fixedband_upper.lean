-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB169_positive_tube_prevents_ae_fixedband_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:08:34.373775+00:00
-- url     : https://prove2.me/submissions/24072b15-b5e3-4863-8d95-755044d32897

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section
/-- Positive event measure contradicts an almost everywhere forbidden cash upper. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hApos : 0 < P A)
    (Q : Ω → Prop)
    (hStrict : ∀ᵐ ω ∂(P.restrict A), ¬ Q ω) :
    ¬ (∀ᵐ ω ∂(P.restrict A), Q ω) := by
  intro hUpper
  have hFalse : ∀ᵐ ω ∂(P.restrict A), False := by
    filter_upwards [hStrict, hUpper] with ω hNot hYes
    exact hNot hYes
  have hZero : P.restrict A = 0 :=
    ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hFalse)
  have hAzero : P A = 0 := (Measure.restrict_eq_zero).mp hZero
  exact (ne_of_gt hApos) hAzero
