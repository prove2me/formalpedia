-- Prove2me | solution 1 for DSGE.nk_equilibrium_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:59:12.372351+00:00
-- url     : https://prove2.me/submissions/b62e9fb1-0a8d-499c-b5b9-6e9f9f34d71d

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
    (y₀ π₀ : ℝ) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ),
      IsNKEquilibrium σ β κ φπ φy p.1 p.2.1 p.2.2 ∧ p.1 0 = y₀ ∧ p.2.1 0 = π₀ := by
  -- the forward map
  let F : ℝ × ℝ → ℝ × ℝ := fun s =>
    ((1 + φy / σ + κ / (σ * β)) * s.1 + ((φπ - 1 / β) / σ) * s.2, (s.2 - κ * s.1) / β)
  let seq : ℕ → ℝ × ℝ := fun t => Nat.rec (y₀, π₀) (fun _ s => F s) t
  have hseq : ∀ t, seq (t + 1) = F (seq t) := fun t => rfl
  let y : ℕ → ℝ := fun t => (seq t).1
  let π : ℕ → ℝ := fun t => (seq t).2
  let i : ℕ → ℝ := fun t => φπ * π t + φy * y t
  have heq : IsNKEquilibrium σ β κ φπ φy y π i := by
    rw [DSGEAux.iff_forward σ β κ φπ φy hσ hβ]
    intro t
    refine ⟨rfl, ?_, ?_⟩
    · show (seq (t + 1)).2 = _; rw [hseq]
    · show (seq (t + 1)).1 = _; rw [hseq]
  refine ⟨(y, π, i), ⟨heq, rfl, rfl⟩, ?_⟩
  rintro ⟨y', π', i'⟩ ⟨h', hy0, hπ0⟩
  simp only at h' hy0 hπ0
  rw [DSGEAux.iff_forward σ β κ φπ φy hσ hβ] at h'
  have hyπ : ∀ t, y' t = y t ∧ π' t = π t := by
    intro t
    induction t with
    | zero => exact ⟨hy0, hπ0⟩
    | succ t ih =>
      obtain ⟨_, hp, hy⟩ := h' t
      refine ⟨?_, ?_⟩
      · rw [hy, ih.1, ih.2]
      · rw [hp, ih.1, ih.2]
  have hy : y' = y := funext fun t => (hyπ t).1
  have hπ : π' = π := funext fun t => (hyπ t).2
  have hi : i' = i := funext fun t => by
    rw [(h' t).1, (hyπ t).1, (hyπ t).2]
  rw [hy, hπ, hi]
