-- Prove2me | solution 1 for CoresConvexGames.Stability.core_subset_stableSet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:20.467538+00:00
-- url     : https://prove2.me/submissions/ba11c452-e59e-46db-bf85-4cf518d4dd6d

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsStableSet

open CoresConvexGames.Stability Supermodularity.Cooperative

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (V : Set (Fin n → ℝ)) (hV : IsStableSet f V) :
    Core Finset.univ f ⊆ V := by
  intro y hy
  obtain ⟨hfeas, hacc⟩ := hy
  obtain ⟨hVfeas, hVchar⟩ := hV
  have hyfeas : IsFeasible f y := le_of_eq hfeas
  rw [hVchar y hyfeas]
  rintro ⟨z, hzV, S, hSne, hzS, hlt⟩
  have h1 : f S ≤ ∑ i ∈ S, y i := hacc S (Finset.subset_univ S)
  have h2 : ∑ i ∈ S, y i < ∑ i ∈ S, z i :=
    Finset.sum_lt_sum_of_nonempty hSne fun i hi => hlt i hi
  linarith
