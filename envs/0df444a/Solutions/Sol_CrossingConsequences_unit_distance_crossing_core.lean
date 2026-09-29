-- Prove2me | solution 1 for CrossingConsequences.unit_distance_crossing_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T19:56:44.50647+00:00
-- url     : https://prove2.me/submissions/6cd27758-1e36-44ff-b7a0-0b36beea1862
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CrossingLemma
import Theorems.Thm_UnitDistanceArcGraph

open Classical
open scoped Real
noncomputable section

theorem solution :
    ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      ∃ e : ℕ,
        (unitDist P : ℝ) - (P.card : ℝ) ≤ (e : ℝ) ∧
        (4 * P.card ≤ e →
          (e : ℝ) ^ 3 / (100 * (P.card : ℝ) ^ 2) ≤
            2 * (P.card : ℝ) ^ 2) := by
  intro P
  rcases UnitDistanceArcGraph P with ⟨G, hGfin, h_edges, h_cross⟩
  letI := hGfin
  refine ⟨G.edgeFinset.card, h_edges, ?_⟩
  intro hlarge
  by_cases hP0 : P.card = 0
  · simp [hP0]
  · have hnP : 1 ≤ P.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hP0)
    have hn : 1 ≤ Fintype.card P := by
      simpa using hnP
    have he : 4 * Fintype.card P ≤ G.edgeFinset.card := by
      simpa using hlarge
    have h_lower := CrossingLemma G hn he
    have h_bound :
        (G.edgeFinset.card : ℝ) ^ 3 /
            (100 * (Fintype.card P : ℝ) ^ 2) ≤
          2 * (P.card : ℝ) ^ 2 :=
      h_lower.trans h_cross
    simpa using h_bound

