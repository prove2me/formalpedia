-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward76_eventwise_HJB_from_vanishing_positive_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:51:28.097199+00:00
-- url     : https://prove2.me/submissions/fc8a0112-c330-4780-ba78-5957c5a7afa4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward35_integrable_positive_residual_event_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (G H : Ω → ℝ) (a : ℝ)
    (hG : Integrable G P) (hH : Integrable H P)
    (hMean : (∫ ω in A, H ω ∂P) ≤ 0)
    (hResidual : ∀ ε : ℝ, 0 < ε →
       (∫ ω in A, max (0 : ℝ) (G ω - a - H ω) ∂P) ≤ ε) :
    (∫ ω in A, G ω ∂P) ≤ a * (P A).toReal := by
  by_contra hn
  have hlt : a * (P A).toReal < (∫ ω in A, G ω ∂P) :=
    lt_of_not_ge hn
  let ε : ℝ := ((∫ ω in A, G ω ∂P) - a * (P A).toReal) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hBudget :=
    AvramDividend.Classical.avram_pj_reward35_integrable_positive_residual_event_budget
      A G H a ε hG hH (hResidual ε hε)
  dsimp [ε] at hBudget
  linarith
