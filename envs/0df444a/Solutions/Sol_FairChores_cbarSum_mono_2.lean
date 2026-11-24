-- Prove2me | solution 2 for FairChores.cbarSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:14.148803+00:00
-- url     : https://prove2.me/submissions/6d44826a-03e3-4df4-a492-bf267e9b9d5b

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbar_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    cbarSum c p A ≤ cbarSum c p B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun t _ _ => cbar_nonneg hc hp t
end FairChores
