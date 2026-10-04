-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.augment_bottleneck
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:29:55.950879+00:00
-- url     : https://prove2.me/submissions/d079ea61-d71d-4509-90ae-1401eaf35f31

import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_simple

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P)
    (u v : V) (hb : IsBottleneck N f P u v) :
    ¬ ResArc N (augment N f P) u v := by
  have hp := hb.1
  have hn := (pathArcs_simple P hP.1 u v hp).2.1
  have he := hb.2
  have hret (x y : V) (hxy : (x, y) ∈ N.A) : ¬ (x = N.t ∧ y = N.s) := by
    rintro ⟨rfl, rfl⟩
    exact N.return_not_mem hxy
  rintro (⟨huv, h⟩ | ⟨hvu, h⟩)
  · by_cases hvu : (v, u) ∈ N.A
    · have h0 := hf.1 v u (Finset.mem_insert_of_mem hvu)
      simp only [stepEps, huv, hvu, ↓reduceIte] at he
      have hm : min (pathEps N f P) (N.c u v - f u v) = N.c u v - f u v :=
        min_eq_right (by linarith)
      simp only [augment, hret u v huv, huv, augIncrease, augDecrease, hp, hn,
        hvu, ↓reduceIte, hm] at h
      linarith
    · simp only [stepEps, huv, hvu, ↓reduceIte] at he
      simp only [augment, hret u v huv, huv, augIncrease, augDecrease, hp, hn,
        hvu, ↓reduceIte] at h
      linarith
  · by_cases huv : (u, v) ∈ N.A
    · have h0 := hf.1 v u (Finset.mem_insert_of_mem hvu)
      simp only [stepEps, huv, hvu, ↓reduceIte] at he
      have hm : max 0 (pathEps N f P - N.c u v + f u v) = f v u := by
        rw [show pathEps N f P - N.c u v + f u v = f v u by linarith]
        exact max_eq_right h0
      simp only [augment, hret v u hvu, hvu, augIncrease, augDecrease, hp, hn,
        huv, ↓reduceIte, hm] at h
      linarith
    · simp only [stepEps, huv, ↓reduceIte] at he
      simp only [augment, hret v u hvu, hvu, augIncrease, augDecrease, hp, hn,
        huv, ↓reduceIte] at h
      linarith
