-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_square_integrable_of_ae_sum_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:16:29.081172+00:00
-- url     : https://prove2.me/submissions/7b838d37-dd7d-423f-94b9-47e9d41b93a4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f G J : α → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hG : Integrable (fun ω => (G ω) ^ 2) μ)
    (hJ : Integrable (fun ω => (J ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ, f ω = G ω + J ω) :
    Integrable (fun ω => (f ω) ^ 2) μ := by
  have hbound : Integrable
      (fun ω => 2 * (G ω) ^ 2 + 2 * (J ω) ^ 2) μ :=
    (hG.const_mul 2).add (hJ.const_mul 2)
  refine hbound.mono' (hf.pow 2) ?_
  filter_upwards [heq] with ω hω
  rw [hω]
  have hb : (G ω + J ω) ^ 2 ≤
      2 * (G ω) ^ 2 + 2 * (J ω) ^ 2 := by
    nlinarith [sq_nonneg (G ω - J ω)]
  have hl : 0 ≤ (G ω + J ω) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hl]
  exact hb
