-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.augment_net_change
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:27:17.884854+00:00
-- url     : https://prove2.me/submissions/b66ebe55-2e87-4760-85a9-dd6e33745896

import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_simple

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsAugPath N f P) (u v : V) :
    (if (u, v) ∈ N.A then augment N f P u v - f u v else 0) -
      (if (v, u) ∈ N.A then augment N f P v u - f v u else 0) =
    (if (u, v) ∈ pathArcs P then pathEps N f P else 0) -
      (if (v, u) ∈ pathArcs P then pathEps N f P else 0) := by
  have hform (x y : V) :
      (if (x, y) ∈ N.A then augment N f P x y - f x y else 0) =
      (if (x, y) ∈ N.A then augIncrease N f P x y - augDecrease N f P x y else 0) := by
    by_cases hxy : (x, y) ∈ N.A
    · have hr : ¬ (x = N.t ∧ y = N.s) := by
        rintro ⟨rfl, rfl⟩
        exact N.return_not_mem hxy
      simp only [augment, hxy, hr, ↓reduceIte]
      ring
    · simp [hxy]
  simp_rw [hform]
  have hstep (x y : V) (hp : (x, y) ∈ pathArcs P) :
      (if (x, y) ∈ N.A then augIncrease N f P x y - augDecrease N f P x y else 0) -
      (if (y, x) ∈ N.A then augIncrease N f P y x - augDecrease N f P y x else 0) =
      pathEps N f P := by
    have hn := (pathArcs_simple P hP.1 x y hp).2.1
    have hr := hP.2.2.2 (x, y) hp
    by_cases hxy : (x, y) ∈ N.A <;> by_cases hyx : (y, x) ∈ N.A
    · simp only [hxy, hyx, augIncrease, augDecrease, hp, hn, ↓reduceIte]
      simp only [min_def, max_def]
      split_ifs <;> linarith
    · simp [hxy, hyx, augIncrease, augDecrease, hp, hn]
    · simp [hxy, hyx, augIncrease, augDecrease, hp, hn]
    · simp [ResArc, hxy, hyx] at hr
  by_cases hp : (u, v) ∈ pathArcs P
  · have hn := (pathArcs_simple P hP.1 u v hp).2.1
    simpa [hp, hn] using hstep u v hp
  · by_cases hp' : (v, u) ∈ pathArcs P
    · have hs := hstep v u hp'
      simp only [hp, hp', ↓reduceIte]
      linarith
    · simp [augIncrease, augDecrease, hp, hp']
