-- Prove2me | solution 1 for FairSelling.TPSset_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T01:35:48.536333+00:00
-- url     : https://prove2.me/submissions/b249c2aa-4c8b-4ae1-bdb2-6d9eeb7146a8

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]


theorem solution (v p : G → ℝ) :
    BddAbove (TPSset n v p) := by
  have bound (s : ℝ) (hs : s ∈ TPSset n v p) : s ≤ PS n v p := by
    apply le_trans hs
    unfold truncSum PS
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun g _ => max_le_max_left _ (min_le_left _ _)) (Nat.cast_nonneg _)
  exact ⟨PS n v p, fun _ hs => bound _ hs⟩
