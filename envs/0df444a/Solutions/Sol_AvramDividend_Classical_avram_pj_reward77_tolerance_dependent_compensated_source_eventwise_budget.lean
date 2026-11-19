-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward77_tolerance_dependent_compensated_source_eventwise_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:51:09.540781+00:00
-- url     : https://prove2.me/submissions/13e709f3-6c30-405c-a5f7-7e45d9cc6e9c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward35_integrable_positive_residual_event_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (G : Ω → ℝ) (a : ℝ)
    (hG : Integrable G P)
    (hSources : ∀ ε : ℝ, 0 < ε →
      ∃ H : Ω → ℝ,
        Integrable H P ∧ (∫ ω in A, H ω ∂P) ≤ 0 ∧
        (∫ ω in A, max (0 : ℝ) (G ω - a - H ω) ∂P) ≤ ε) :
    (∫ ω in A, G ω ∂P) ≤ a * (P A).toReal := by
  by_contra hn
  have hlt : a * (P A).toReal < (∫ ω in A, G ω ∂P) :=
    lt_of_not_ge hn
  let ε : ℝ := ((∫ ω in A, G ω ∂P) - a * (P A).toReal) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨H, hHI, hMean, hRes⟩ := hSources ε hε
  have hBound :=
    AvramDividend.Classical.avram_pj_reward35_integrable_positive_residual_event_budget
      A G H a ε hG hHI hRes
  dsimp [ε] at hBound
  linarith
