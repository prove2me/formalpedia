-- Prove2me | solution 1 for ConsHalving.Additive.step_3_invariant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:02:09.737476+00:00
-- url     : https://prove2.me/submissions/64e7642e-b731-4e8e-8402-a28e239b0aaf

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting
import Theorems.Thm_ConsHalving_Additive_eq_1_iff
import Theorems.Thm_ConsHalving_Additive_affine_comb_solves
import Theorems.Thm_ConsHalving_Additive_step_3c_bounds

open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsConsensusHalving u x) (hT : ∀ j ∈ T, x j = 0 ∨ x j = 1)
    (hy : SolvesST u T x y) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsConsensusHalving u (stepPoint x y (gamma x y jstar)) ∧ jstar ∉ T ∧
      ∀ j ∈ insert jstar T,
        stepPoint x y (gamma x y jstar) j = 0 ∨ stepPoint x y (gamma x y jstar) j = 1 := by
  have conv : ∀ (z : Fin m → ℝ) (i : Fin n),
      ∑ j, (z j - 1 / 2) * u i j = ∑ j, z j * u i j - 1 / 2 * ∑ j, u i j := by
    intro z i
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- `x` solves the system `S`, by equation (1)
  have hxS : SolvesS u x := by
    intro i
    have := (eq_1_iff u x).1 hx.2 i
    rw [conv]; linarith
  obtain ⟨hfrac, hfix, hend⟩ := step_3c_bounds x y jstar hx.1 hstar hmin
  have hsS : SolvesS u (stepPoint x y (gamma x y jstar)) :=
    affine_comb_solves u x y _ hxS hy.1
  have hnotT : jstar ∉ T := fun h => hstar (hy.2 jstar h)
  refine ⟨⟨hfrac, (eq_1_iff u _).2 fun i => ?_⟩, hnotT, fun j hj => ?_⟩
  · have := hsS i
    rw [conv] at this; linarith
  · rcases Finset.mem_insert.1 hj with rfl | hjT
    · exact hend
    · rw [hfix j (hy.2 j hjT)]
      exact hT j hjT
