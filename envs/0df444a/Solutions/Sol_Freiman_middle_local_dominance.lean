-- Prove2me | solution 1 for Freiman.middle_local_dominance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:35:39.07817+00:00
-- url     : https://prove2.me/submissions/9833566c-8368-4c06-81d9-773aa6afc1c7

import Theorems.Thm_Freiman_middle_small_digit_centers
import Theorems.Thm_Freiman_middle_secondary_four_bound
import Theorems.Thm_Freiman_middle_adjacent_four_identity
import Theorems.Thm_Freiman_middle_secondary_four_separations

open Freiman

theorem solution :
    ∀ (r : Fin 15) (a : ℤ→ℕ+) (t : ℝ), middleCompatible (middleRoot r) a → localValue a 0=t → Real.sqrt 21 ≤ t → ∀ i : ℤ, localValue a i ≤ t := by
  intro r a t hc ht hlo i
  by_cases h : (a i:ℕ) ≤ 3
  · exact le_trans (middle_small_digit_centers r a i hc h) hlo
  · exact (middle_secondary_four_bound middle_adjacent_four_identity middle_secondary_four_separations r a i hc h).trans (le_of_eq ht)
