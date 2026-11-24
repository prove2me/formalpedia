-- Prove2me | solution 1 for FairChores.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:46.330836+00:00
-- url     : https://prove2.me/submissions/e2764824-a9cd-47ff-964b-9374d8575639

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbar_nonneg
import Theorems.Thm_FairChores_cbar_le_wt

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (t : T) : 0 ≤ wt c p mu t :=
  le_trans (cbar_nonneg hc hp t) (cbar_le_wt t)
end FairChores
