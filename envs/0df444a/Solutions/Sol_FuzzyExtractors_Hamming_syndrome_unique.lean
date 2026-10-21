-- Prove2me | solution 1 for FuzzyExtractors.Hamming.syndrome_unique
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T12:10:32.682324+00:00
-- url     : https://prove2.me/submissions/f23a5fbe-9bda-4aa4-a107-01e81a25bdc9

import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Lean.Elab.Tactic.Omega

theorem solution {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k t : ℕ}
    (C : Submodule F (Fin n → F)) (hk : Module.finrank F C = k)
    (syn : (Fin n → F) →ₗ[F] (Fin (n - k) → F)) (hsyn : LinearMap.ker syn = C)
    (hdist : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * t + 1 ≤ hammingDist c c')
    (w' v₁ v₂ : Fin n → F) (h₁ : hammingDist v₁ w' ≤ t) (h₂ : hammingDist v₂ w' ≤ t)
    (hs : syn v₁ = syn v₂) : v₁ = v₂ := by
  classical
  have hmem : v₁ - v₂ ∈ C := by
    rw [← hsyn, LinearMap.mem_ker]
    rw [map_sub, hs, sub_self]
  by_contra hne
  have hsep := hdist (v₁ - v₂) hmem 0 C.zero_mem (sub_ne_zero.mpr hne)
  have hd : hammingDist (v₁ - v₂) 0 = hammingDist v₁ v₂ := by
    simp only [hammingDist, Pi.sub_apply, Pi.zero_apply, ne_eq, sub_eq_zero]
  rw [hd] at hsep
  have hupper := hammingDist_triangle_right v₁ v₂ w'
  omega

#print axioms solution
