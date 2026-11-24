-- Prove2me | solution 2 for FairSelling.TPSset_le_PS
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T01:37:55.259884+00:00
-- url     : https://prove2.me/submissions/5842a0b5-eed4-41b3-a731-e0ffef351bd0

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]


theorem solution (v p : G → ℝ) {t : ℝ} (ht : t ∈ TPSset n v p) :
    t ≤ PS n v p := by
  have bound (s : ℝ) (hs : s ∈ TPSset n v p) : s ≤ PS n v p := by
    apply le_trans hs
    unfold truncSum PS
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun g _ => max_le_max_left _ (min_le_left _ _)) (Nat.cast_nonneg _)
  exact bound t ht
