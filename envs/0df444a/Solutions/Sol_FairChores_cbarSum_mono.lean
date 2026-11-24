-- Prove2me | solution 1 for FairChores.cbarSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:22:36.715303+00:00
-- url     : https://prove2.me/submissions/84c5a521-bce7-4eed-99f5-f9d4df2c30c8

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]


theorem solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    cbarSum c p A ≤ cbarSum c p B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h; intro t _ _; exact le_min (hc t) (hp t)
