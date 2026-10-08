-- Prove2me | solution 1 for AvramDividend.Classical.eventual_psi_above_q_of_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:47:41.456818+00:00
-- url     : https://prove2.me/submissions/703dfd8c-2afd-4dbc-bf4d-8d85d1716783

import Mathlib

open Filter

theorem solution
    (ψ : ℝ → ℝ) (q : ℝ)
    (hψ : Tendsto ψ atTop atTop) :
    ∃ β0 : ℝ, 0 ≤ β0 ∧
      ∀ θ : ℝ, β0 ≤ θ → q < ψ θ := by
  have hlarge : ∀ᶠ θ : ℝ in atTop, q + 1 ≤ ψ θ :=
    (tendsto_atTop.1 hψ) (q + 1)
  obtain ⟨B, hB⟩ := eventually_atTop.1 hlarge
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro θ hθ
  have hge : q + 1 ≤ ψ θ :=
    hB θ (le_trans (le_max_right _ _) hθ)
  linarith
