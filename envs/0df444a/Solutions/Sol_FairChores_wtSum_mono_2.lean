-- Prove2me | solution 2 for FairChores.wtSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:57.586191+00:00
-- url     : https://prove2.me/submissions/3f10146c-d5fb-415e-bfea-6535dbc2f7f4

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_wt_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    wtSum c p mu A ≤ wtSum c p mu B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun t _ _ => wt_nonneg hc hp t
end FairChores
