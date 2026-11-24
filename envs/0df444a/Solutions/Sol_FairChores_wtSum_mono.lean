-- Prove2me | solution 1 for FairChores.wtSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:29:18.348587+00:00
-- url     : https://prove2.me/submissions/54884e85-9978-49e0-9d28-f23d30f5f87f

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]


theorem solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    wtSum c p mu A ≤ wtSum c p mu B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h; intro t _ _; unfold wt; split <;> first | exact hp t | exact le_min (hc t) (hp t)
