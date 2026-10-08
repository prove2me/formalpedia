-- Prove2me | solution 1 for ConjugateConvex.Involution.subset_biconjDomain_and_biconjFun_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:55:17.368249+00:00
-- url     : https://prove2.me/submissions/daa73328-fa4c-4bef-ad6c-b8d2325b2272

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

open ConjugateConvex.Involution in
theorem solution {n : ℕ} (G : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (hΓ : (conjDomain G f).Nonempty) :
    ∀ x ∈ G, x ∈ conjDomain (conjDomain G f) (conjFun G f) ∧
      conjFun (conjDomain G f) (conjFun G f) x ≤ f x := by
  intro x hx
  have key : ∀ ξ ∈ conjDomain G f, ξ ⬝ᵥ x - conjFun G f ξ ≤ f x := by
    intro ξ hξ
    have h1 : x ⬝ᵥ ξ - f x ≤ conjFun G f ξ :=
      le_csSup hξ ⟨x, hx, rfl⟩
    rw [dotProduct_comm] at h1
    linarith
  have hub : ∀ y ∈ (fun ξ => ξ ⬝ᵥ x - conjFun G f ξ) '' conjDomain G f, y ≤ f x := by
    rintro y ⟨ξ, hξ, rfl⟩
    exact key ξ hξ
  refine ⟨⟨f x, hub⟩, ?_⟩
  exact csSup_le (hΓ.image _) hub
