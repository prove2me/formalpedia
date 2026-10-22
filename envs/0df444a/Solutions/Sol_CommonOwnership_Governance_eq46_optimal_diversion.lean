-- Prove2me | solution 1 for CommonOwnership.Governance.eq46_optimal_diversion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:26:38.264671+00:00
-- url     : https://prove2.me/submissions/855f90c8-7a0b-4ca8-b72c-8cfded2b1eea

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
import Definitions.Def_CommonOwnership_Governance_DiversionModel
set_option autoImplicit false
open CommonOwnership.Governance

theorem solution (β φ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hφ : 1 ≤ φ) :
    IsOptDiversion (divCost φ) β (fun s => (1 - (β - s)) / φ) ∧
      ∀ adiv : ℝ → ℝ, IsOptDiversion (divCost φ) β adiv →
        ∀ s ∈ Set.Icc (0:ℝ) β, adiv s = (1 - (β - s)) / φ := by
  have hφ0 : 0 < φ := by linarith
  have key : ∀ s a : ℝ, divertObj (divCost φ) β s ((1 - (β - s)) / φ) - divertObj (divCost φ) β s a
      = φ / 2 * (a - (1 - (β - s)) / φ) ^ 2 := by
    intro s a
    unfold divertObj divCost
    field_simp
    ring
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) β, (1 - (β - s)) / φ ∈ Set.Icc (0:ℝ) 1 := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_one hφ0]; linarith
  constructor
  · intro s hs
    refine ⟨hmem s hs, ?_⟩
    intro a _
    have := key s a
    have h2 : 0 ≤ φ / 2 * (a - (1 - (β - s)) / φ) ^ 2 := by positivity
    linarith
  · intro adiv hopt s hs
    obtain ⟨_, hmax⟩ := hopt s hs
    have h1 := hmax _ (hmem s hs)
    have h2 := key s (adiv s)
    have h3 : φ / 2 * (adiv s - (1 - (β - s)) / φ) ^ 2 ≤ 0 := by linarith
    have h4 : (adiv s - (1 - (β - s)) / φ) ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have : 0 < φ / 2 * (adiv s - (1 - (β - s)) / φ) ^ 2 := by positivity
      linarith
    have h5 : adiv s - (1 - (β - s)) / φ = 0 := by
      apply pow_eq_zero_iff (two_ne_zero) |>.1
      exact le_antisymm h4 (sq_nonneg _)
    linarith
