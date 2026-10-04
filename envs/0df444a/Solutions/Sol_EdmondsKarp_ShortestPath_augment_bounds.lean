-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.augment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:27:16.222272+00:00
-- url     : https://prove2.me/submissions/c452ec13-7775-45ce-a5a0-aed7dd75d3a8

import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_simple
import Theorems.Thm_EdmondsKarp_ShortestPath_pathEps_bounds

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    (∀ u v, (u, v) ∈ N.A →
      0 ≤ augment N f P u v ∧ augment N f P u v ≤ N.c u v) ∧
    augment N f P N.t N.s = f N.t N.s + pathEps N f P := by
  obtain ⟨hepos, hele, _⟩ := pathEps_bounds N f P hf hP
  refine ⟨?_, by simp [augment]⟩
  intro u v huv
  have h0 := hf.1 u v (Finset.mem_insert_of_mem huv)
  have hc := hf.2.1 u v huv
  have hr : ¬ (u = N.t ∧ v = N.s) := by
    rintro ⟨rfl, rfl⟩
    exact N.return_not_mem huv
  by_cases hp : (u, v) ∈ pathArcs P
  · have hn := (pathArcs_simple P hP.1 u v hp).2.1
    have he := hele (u, v) hp
    by_cases hvu : (v, u) ∈ N.A
    · simp only [augment, hr, huv, augIncrease, augDecrease, hp, hn, hvu, ↓reduceIte]
      constructor
      · simpa only [sub_zero] using add_nonneg h0 (le_min hepos.le (sub_nonneg.mpr hc))
      · linarith [min_le_right (pathEps N f P) (N.c u v - f u v)]
    · simp only [stepEps, huv, hvu, ↓reduceIte] at he
      simp only [augment, hr, huv, augIncrease, augDecrease, hp, hn, hvu, ↓reduceIte]
      constructor <;> linarith
  · by_cases hp' : (v, u) ∈ pathArcs P
    · have he := hele (v, u) hp'
      by_cases hvu : (v, u) ∈ N.A
      · simp only [stepEps, huv, hvu, ↓reduceIte] at he
        simp only [augment, hr, huv, augIncrease, augDecrease, hp, hp', hvu, ↓reduceIte]
        rw [add_zero]
        constructor
        · exact sub_nonneg.mpr (max_le h0 (by linarith))
        · linarith [le_max_left (0 : ℝ) (pathEps N f P - N.c v u + f v u)]
      · simp only [stepEps, hvu, ↓reduceIte] at he
        simp only [augment, hr, huv, augIncrease, augDecrease, hp, hp', hvu, ↓reduceIte]
        constructor <;> linarith
    · simpa [augment, hr, huv, augIncrease, augDecrease, hp, hp'] using And.intro h0 hc
