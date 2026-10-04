-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.pathEps_bounds
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:27:20.914462+00:00
-- url     : https://prove2.me/submissions/b43a3564-5c0c-471c-a403-c9c6c983b713

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    0 < pathEps N f P ∧
    (∀ e ∈ pathArcs P, pathEps N f P ≤ stepEps N f e.1 e.2) ∧
    ∃ u v, IsBottleneck N f P u v := by
  have hpos : ∀ e ∈ pathArcs P, 0 < stepEps N f e.1 e.2 := by
    intro ⟨u, v⟩ he
    have hr := hP.2.2.2 (u, v) he
    have hnonneg : ∀ x y, (x, y) ∈ N.A → 0 ≤ f x y := by
      intro x y hxy
      exact hf.1 x y (Finset.mem_insert_of_mem hxy)
    by_cases huv : (u, v) ∈ N.A
    · by_cases hvu : (v, u) ∈ N.A
      · have hc := hf.2.1 u v huv
        have hn := hnonneg v u hvu
        simp only [stepEps, huv, hvu, ↓reduceIte]
        rcases hr with hr | hr <;> linarith [hr.2]
      · simpa [stepEps, huv, hvu, ResArc] using hr
    · rcases hr with hr | hr
      · exact (huv hr.1).elim
      · simpa [stepEps, huv] using hr.2
  have hne : pathArcs P ≠ [] := by
    rcases P with _ | ⟨a, _ | ⟨b, L⟩⟩
    · simp [IsAugPath, IsDirPath] at hP
    · have hs : a = N.s := by simpa using hP.2.1
      have ht : a = N.t := by simpa using hP.2.2.1
      exact (N.source_ne_sink (hs.symm.trans ht)).elim
    · simp [pathArcs]
  let E := (pathArcs P).map (fun e => stepEps N f e.1 e.2)
  have hE : E ≠ [] := by simpa [E] using hne
  cases hm : E.min? with
  | none => exact (hE (List.min?_eq_none_iff.mp hm)).elim
  | some m =>
    have hmin := List.min?_eq_some_iff.mp hm
    obtain ⟨e, he, hem⟩ := List.mem_map.mp hmin.1
    have heps : pathEps N f P = m := by
      change E.min?.getD 0 = m
      simp [hm]
    refine ⟨?_, ?_, e.1, e.2, he, ?_⟩
    · rw [heps, ← hem]
      exact hpos e he
    · intro d hd
      rw [heps]
      exact hmin.2 _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
    · exact hem.trans heps.symm
