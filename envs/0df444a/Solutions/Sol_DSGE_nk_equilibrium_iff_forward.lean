-- Prove2me | solution 1 for DSGE.nk_equilibrium_iff_forward
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:59:05.257559+00:00
-- url     : https://prove2.me/submissions/2f487e58-be55-45d1-813e-90a7ae74984f

import Mathlib
import Definitions.Def_DSGE_NK_model
open DSGE

namespace DSGEAux

lemma iff_forward (σ β κ φπ φy : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0)
    (y π i : ℕ → ℝ) :
    IsNKEquilibrium σ β κ φπ φy y π i ↔
      ∀ t : ℕ,
        i t = φπ * π t + φy * y t ∧
        π (t + 1) = (π t - κ * y t) / β ∧
        y (t + 1) = (1 + φy / σ + κ / (σ * β)) * y t + ((φπ - 1 / β) / σ) * π t := by
  unfold IsNKEquilibrium
  constructor
  · intro h t
    obtain ⟨h1, h2, h3⟩ := h t
    have hp : π (t + 1) = (π t - κ * y t) / β := by
      field_simp; linarith
    refine ⟨h3, hp, ?_⟩
    rw [hp, h3] at h1
    field_simp at h1 ⊢
    linear_combination -h1
  · intro h t
    obtain ⟨h3, hp, hy⟩ := h t
    refine ⟨?_, ?_, h3⟩
    · rw [hy, hp, h3]; field_simp; ring
    · rw [hp]; field_simp; ring

end DSGEAux

theorem solution (σ β κ φπ φy : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0)
    (y π i : ℕ → ℝ) :
    IsNKEquilibrium σ β κ φπ φy y π i ↔
      ∀ t : ℕ,
        i t = φπ * π t + φy * y t ∧
        π (t + 1) = (π t - κ * y t) / β ∧
        y (t + 1) = (1 + φy / σ + κ / (σ * β)) * y t + ((φπ - 1 / β) / σ) * π t :=
  DSGEAux.iff_forward σ β κ φπ φy hσ hβ y π i
