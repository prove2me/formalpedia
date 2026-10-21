-- Prove2me | solution 1 for BudgetClock.Subadditive.subadditive_cover
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:33:48.442278+00:00
-- url     : https://prove2.me/submissions/a755ac46-52b3-461a-a86a-d87d44d8ac90

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Setting

set_option autoImplicit false
open BudgetClock.Subadditive

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hsub : IsSubadditive v)
    (r : ℕ) (Z : Fin (r + 1) → Finset (Fin n)) (O : Finset (Fin n))
    (hO : O = Finset.univ.biUnion Z) :
    v O ≤ ∑ i : Fin (r + 1), v (Z i) := by
  subst hO
  induction r with
  | zero =>
    simp
  | succ r ih =>
    have h1 := ih (fun i => Z i.castSucc)
    rw [Fin.sum_univ_castSucc]
    have h2 : (Finset.univ.biUnion Z : Finset (Fin n)) =
        (Finset.univ.biUnion (fun i : Fin (r + 1) => Z i.castSucc)) ∪ Z (Fin.last (r + 1)) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Or.inl ⟨j, hi⟩
        · exact Or.inr hi
      · rintro (⟨j, hj⟩ | h)
        · exact ⟨j.castSucc, hj⟩
        · exact ⟨_, h⟩
    rw [h2]
    have := hsub (Finset.univ.biUnion (fun i : Fin (r + 1) => Z i.castSucc)) (Z (Fin.last (r + 1)))
    linarith

