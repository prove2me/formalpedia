-- Prove2me | solution 1 for CommonOwnership.Governance.eq21_optimal_monitoring
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:17:44.723823+00:00
-- url     : https://prove2.me/submissions/1f462136-7c77-4eec-a475-79c43ae3f49b

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
set_option autoImplicit false

open CommonOwnership.Governance

theorem solution (β ξ γ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ)
    (hγ : ξ < γ) :
    IsOptMonitoring (quadCost γ) ξ β (fun t => ξ * t / γ) ∧
      ∀ mstar : ℝ → ℝ, IsOptMonitoring (quadCost γ) ξ β mstar →
        ∀ t ∈ Set.Icc (0:ℝ) β, mstar t = ξ * t / γ := by
  have hγ0 : 0 < γ := lt_trans hξ hγ
  -- the objective as a perfect square
  have hdiff : ∀ t m : ℝ, monitorObj (quadCost γ) ξ t (ξ * t / γ) - monitorObj (quadCost γ) ξ t m
      = γ / 2 * (m - ξ * t / γ) ^ 2 := by
    intro t m
    unfold monitorObj quadCost
    field_simp
    ring
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) β, ξ * t / γ ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    refine ⟨by have := ht.1; positivity, ?_⟩
    rw [div_le_one hγ0]
    nlinarith [ht.2, ht.1]
  refine ⟨?_, ?_⟩
  · intro t ht
    refine ⟨hmem t ht, ?_⟩
    intro m _
    have := hdiff t m
    have h2 : 0 ≤ γ / 2 * (m - ξ * t / γ) ^ 2 := by positivity
    linarith
  · intro mstar hopt t ht
    obtain ⟨_, hmax⟩ := hopt t ht
    have h1 := hmax (ξ * t / γ) (hmem t ht)
    have h2 := hdiff t (mstar t)
    have h3 : γ / 2 * (mstar t - ξ * t / γ) ^ 2 ≤ 0 := by linarith
    have h4 : (mstar t - ξ * t / γ) ^ 2 = 0 := by
      have : 0 ≤ (mstar t - ξ * t / γ) ^ 2 := sq_nonneg _
      nlinarith
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h4
    linarith
