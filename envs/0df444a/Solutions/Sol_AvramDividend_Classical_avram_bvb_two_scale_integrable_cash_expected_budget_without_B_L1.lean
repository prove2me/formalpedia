-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_two_scale_integrable_cash_expected_budget_without_B_L1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:10:02.311529+00:00
-- url     : https://prove2.me/submissions/dec88482-260b-42f9-9bcc-21eab525b2bf

import Mathlib
open MeasureTheory
open scoped Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (a : ℝ) (F M B E₁ E₂ : Ω → ℝ)
    (hF : Integrable F P)
    (hM : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0)
    (hE₁ : Integrable (fun ω => max (E₁ ω) 0) P)
    (hE₂ : Integrable (fun ω => max (E₂ ω) 0) P)
    (hB : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω + max (E₁ ω) 0 + max (E₂ ω) 0) :
    (∫ ω, F ω ∂P) ≤ a +
      (∫ ω, max (E₁ ω) 0 ∂P) +
      (∫ ω, max (E₂ ω) 0 ∂P) := by
  have h1 : Integrable (fun ω => a + M ω) P := (integrable_const a).add hM
  have h2 : Integrable (fun ω => a + M ω + max (E₁ ω) 0) P := h1.add hE₁
  have h3 : Integrable (fun ω => a + M ω + max (E₁ ω) 0 + max (E₂ ω) 0) P := h2.add hE₂
  have hle : ∀ᵐ ω ∂P, F ω ≤ a + M ω + max (E₁ ω) 0 + max (E₂ ω) 0 := by
    filter_upwards [hB, hBudget] with ω h1 h2
    linarith
  calc (∫ ω, F ω ∂P) ≤ ∫ ω, (a + M ω + max (E₁ ω) 0 + max (E₂ ω) 0) ∂P :=
        integral_mono_ae hF h3 hle
    _ = a + (∫ ω, max (E₁ ω) 0 ∂P) + (∫ ω, max (E₂ ω) 0 ∂P) := by
      rw [integral_add h2 hE₂, integral_add h1 hE₁, integral_add (integrable_const a) hM, hM0]
      simp
