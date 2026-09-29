-- Prove2me | solution 1 for CoresConvexGames.Stability.stableSet_not_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:29.827412+00:00
-- url     : https://prove2.me/submissions/94c57ca0-8ece-4301-9461-c52ceb35a2fd

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_IsStableSet

open CoresConvexGames.Stability

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (V W : Set (Fin n → ℝ)) (hV : IsStableSet f V) (hW : IsStableSet f W) :
    ¬ V ⊂ W := by
  intro hss
  have hsub : V ⊆ W := subset_of_ssubset hss
  obtain ⟨w, hwW, hwV⟩ := Set.exists_of_ssubset hss
  have hfeas : IsFeasible f w := hW.1 w hwW
  have hdomex : ∃ a ∈ V, Dominates f a w := by
    by_contra hc
    exact hwV ((hV.2 w hfeas).mpr hc)
  obtain ⟨a, haV, hdom⟩ := hdomex
  exact (hW.2 w hfeas).mp hwW ⟨a, hsub haV, hdom⟩
