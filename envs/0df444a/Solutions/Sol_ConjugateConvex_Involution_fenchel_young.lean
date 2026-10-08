-- Prove2me | solution 1 for ConjugateConvex.Involution.fenchel_young
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:56:29.115325+00:00
-- url     : https://prove2.me/submissions/5fee5d63-7f56-4add-9888-9caac9bdd572

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

set_option autoImplicit false

open ConjugateConvex.Involution in
theorem solution {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    ∀ x ∈ G, ∀ ξ ∈ conjDomain G f, x ⬝ᵥ ξ ≤ f x + conjFun G f ξ := by
  intro x hx ξ hξ
  have h : x ⬝ᵥ ξ - f x ≤ conjFun G f ξ := le_csSup hξ ⟨x, hx, rfl⟩
  linarith

#print axioms solution
