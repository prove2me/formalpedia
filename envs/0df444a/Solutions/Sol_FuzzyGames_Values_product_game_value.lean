-- Prove2me | solution 1 for FuzzyGames.Values.product_game_value
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:04.194989+00:00
-- url     : https://prove2.me/submissions/6e467131-16f4-445b-84c7-2465be9f0134

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

open FuzzyGames.Values

theorem solution (ψ : (n : ℕ) → Vn n → (Fin n → ℝ))
    (hP : IsParetoOptimal ψ) (hS : IsSymmetric ψ) (n : ℕ) (hn : 0 < n) (v : Vn n)
    (hv : ∀ τ : Fin n → ℝ, v.1 τ = ∏ i, τ i) :
    ψ n v = (v.1 1 / n) • (1 : Fin n → ℝ)  := by
  classical
  have heq (i j : Fin n) : ψ n v i = ψ n v j := by
    have h := hS n hn (Equiv.swap i j) v v (fun τ => by
      rw [hv, hv]
      exact ((Equiv.swap i j).symm.prod_comp τ).symm) i
    simpa using h
  ext i
  have hp := hP n hn v
  have hs : (∑ j, ψ n v j) = (n : ℝ) * ψ n v i := by
    simp_rw [heq _ i]
    simp
  rw [hs] at hp
  simpa using (eq_div_iff (by exact_mod_cast Nat.ne_of_gt hn)).mpr (by linarith : ψ n v i * (n : ℝ) = v.1 1)

#print axioms solution

