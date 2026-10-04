-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.augment_residual_sub
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:29:56.694134+00:00
-- url     : https://prove2.me/submissions/550f489e-2a5e-4aa6-a431-4e1bbf62f402

import Theorems.Thm_EdmondsKarp_ShortestPath_pathEps_bounds

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P)
    (u v : V) (h : ResArc N (augment N f P) u v) :
    ResArc N f u v ∨ (v, u) ∈ pathArcs P := by
  have he := (pathEps_bounds N f P hf hP).1.le
  by_cases hp : (v, u) ∈ pathArcs P
  · exact Or.inr hp
  left
  have hret (x y : V) (hxy : (x, y) ∈ N.A) : ¬ (x = N.t ∧ y = N.s) := by
    rintro ⟨rfl, rfl⟩
    exact N.return_not_mem hxy
  rcases h with ⟨huv, h⟩ | ⟨hvu, h⟩
  · left
    refine ⟨huv, ?_⟩
    have hinc : 0 ≤ augIncrease N f P u v := by
      have hc := sub_nonneg.mpr (hf.2.1 u v huv)
      unfold augIncrease
      split_ifs <;> first | exact le_min he hc | exact he | exact le_rfl
    simp only [augment, hret u v huv, huv, augDecrease, hp, ↓reduceIte] at h
    linarith
  · right
    refine ⟨hvu, ?_⟩
    have hdec : 0 ≤ augDecrease N f P v u := by
      unfold augDecrease
      split_ifs <;> first | exact le_max_left _ _ | exact he | exact le_rfl
    simp only [augment, hret v u hvu, hvu, augIncrease, hp, ↓reduceIte] at h
    linarith
