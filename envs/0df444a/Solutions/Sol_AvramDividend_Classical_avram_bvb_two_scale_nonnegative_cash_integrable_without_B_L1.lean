-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_two_scale_nonnegative_cash_integrable_without_B_L1
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-15T15:14:02.73922+00:00
-- url     : https://prove2.me/submissions/c7c737a3-302a-438e-a2c7-a6b6cec8b848

import Mathlib
open MeasureTheory



theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (a : ℝ) (F M B E₁ E₂ : Ω → ℝ),
    AEStronglyMeasurable F P →
    (∀ᵐ ω ∂P, 0 ≤ F ω) →
    Integrable M P →
    Integrable (fun ω => max (E₁ ω) 0) P →
    Integrable (fun ω => max (E₂ ω) 0) P →
    (∀ᵐ ω ∂P, B ω ≤ 0) →
    (∀ᵐ ω ∂P, F ω ≤ a + M ω + B ω + max (E₁ ω) 0 + max (E₂ ω) 0) →
    Integrable F P) := by
  intro h
  have := @h PUnit.{1} _ ((⊤ : ENNReal) • Measure.dirac (PUnit.unit : PUnit.{1})) 1 (fun _ => 1) 0 0 0 0
    aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => zero_le_one) (integrable_zero _ _ _)
    (by simp) (by simp)
    (Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun _ => by simp)
  rw [integrable_const_iff] at this
  rcases this with h1 | h1
  · norm_num at h1
  · have := h1.measure_univ_lt_top
    simp at this
