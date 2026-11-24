-- Prove2me | solution 1 for FairSelling.TPS_le_PS
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T01:35:59.538092+00:00
-- url     : https://prove2.me/submissions/7a454dd3-98df-4f33-b94f-4b597471b4d6

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]


theorem solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    TPS n v p ≤ PS n v p := by
  have bound (s : ℝ) (hs : s ∈ TPSset n v p) : s ≤ PS n v p := by
    apply le_trans hs
    unfold truncSum PS
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun g _ => max_le_max_left _ (min_le_left _ _)) (Nat.cast_nonneg _)
  apply csSup_le _ bound
  refine ⟨0,?_⟩
  show 0 ≤ (∑ g, max (p g) (min (v g) 0)) / (n : ℝ)
  exact div_nonneg (Finset.sum_nonneg fun g _ => (hp g).trans (le_max_left _ _)) (Nat.cast_nonneg _)
