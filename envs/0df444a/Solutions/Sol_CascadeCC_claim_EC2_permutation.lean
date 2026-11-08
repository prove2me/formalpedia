-- Prove2me | solution 1 for CascadeCC.claim_EC2_permutation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:51:36.211749+00:00
-- url     : https://prove2.me/submissions/6b634858-45d9-45eb-9943-3cb4eb621a29

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace Aux_CascadeCC_EC2
open CascadeCC

theorem aux {J : ℕ} (M : Instance J) (n : ℕ) (π : Equiv.Perm (Fin n)) :
    ∀ k j, J - j ≤ k → ∀ (σ : Fin n → ℝ) (z : Fin J → ℝ), Rev M n j (σ ∘ π) z = Rev M n j σ z := by
  intro k
  induction k with
  | zero =>
    intro j hj σ z
    have h : ¬ j < J := by omega
    conv_lhs => rw [Rev]
    conv_rhs => rw [Rev]
    rw [dif_neg h, dif_neg h]
  | succ k ih =>
    intro j hj σ z
    conv_lhs => rw [Rev]
    conv_rhs => rw [Rev]
    by_cases h : j < J
    · rw [dif_pos h, dif_pos h]
      congr 1
      ext y
      constructor
      · rintro ⟨α, ⟨hα1, hα2⟩, rfl⟩
        have hs : ∀ g : Fin n → ℝ → ℝ, ∑ t, g t (α (π.symm t)) = ∑ t, g (π t) (α t) := by
          intro g
          rw [← Equiv.sum_comp π]; simp
        refine ⟨α ∘ π.symm, ⟨fun t => hα1 _, ?_⟩, ?_⟩
        · have := hs (fun t x => σ t * x)
          simp only [Function.comp] at this hα2 ⊢
          rw [this]; exact hα2
        · have h1 := hs (fun t x => σ t * x)
          have h2 := hs (fun t x => σ t * M.r ⟨j, h⟩ x)
          simp only [Function.comp] at h1 h2 ⊢
          rw [h1, h2, ← ih (j + 1) (by omega)]
          congr 2
          funext t
          simp
      · rintro ⟨β, ⟨hβ1, hβ2⟩, rfl⟩
        have hs : ∀ g : Fin n → ℝ → ℝ, ∑ t, g (π t) (β (π t)) = ∑ t, g t (β t) := by
          intro g
          exact Equiv.sum_comp π (fun t => g t (β t))
        refine ⟨β ∘ π, ⟨fun t => hβ1 _, ?_⟩, ?_⟩
        · have := hs (fun t x => σ t * x)
          simp only [Function.comp] at this hβ2 ⊢
          rw [this]; exact hβ2
        · have h1 := hs (fun t x => σ t * x)
          have h2 := hs (fun t x => σ t * M.r ⟨j, h⟩ x)
          simp only [Function.comp] at h1 h2 ⊢
          rw [h1, h2]
          have := ih (j + 1) (by omega)
            (fun t => σ t * M.zeta ⟨j, h⟩ - M.zeta ⟨j, h⟩ * σ t * β t)
            (Function.update z ⟨j, h⟩ (z ⟨j, h⟩ - ∑ t, σ t * β t))
          simp only [Function.comp_def] at this
          rw [this]
    · rw [dif_neg h, dif_neg h]

end Aux_CascadeCC_EC2

open CascadeCC Aux_CascadeCC_EC2 in
theorem solution {J : ℕ} (M : Instance J) (n j : ℕ) (σ : Fin n → ℝ) (z : Fin J → ℝ)
    (π : Equiv.Perm (Fin n)) : Rev M n j (σ ∘ π) z = Rev M n j σ z :=
  aux M n π (J - j) j le_rfl σ z
