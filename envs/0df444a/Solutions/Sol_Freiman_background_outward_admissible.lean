-- Prove2me | solution 1 for Freiman.background_outward_admissible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:42.122147+00:00
-- url     : https://prove2.me/submissions/457812b2-dbe4-4db3-80bf-cd0c12b938a1

import Theorems.Thm_Freiman_background_outward_constraints
import Theorems.Thm_Freiman_background_automaton_correct

open Freiman

theorem solution (a : ℤ → ℕ+) (i : ℤ)
    (ha : ∀ j : ℤ, (a j : ℕ) ≤ 4)
    (h14 : AvoidsBlock a [1,4]) (h41 : AvoidsBlock a [4,1])
    (h31313 : AvoidsBlock a [3,1,3,1,3]) (hi : (a i : ℕ) = 3) :
    ∀ r : Bool,
      (∀ n : ℕ, (backgroundOutward a i r n : ℕ) ≤ 4) ∧
      OneSidedAvoidsBlock (backgroundOutward a i r) [1,4] ∧
      BackgroundAllowed .three (backgroundOutward a i r) := by
  intro r
  obtain ⟨hbound, hpairs, havoid⟩ := background_outward_constraints a i ha h14 h41 h31313 hi r
  refine ⟨hbound, hpairs, ?_⟩
  apply (background_automaton_correct .three (backgroundOutward a i r)).2
  simpa only [backgroundStateWord] using havoid

