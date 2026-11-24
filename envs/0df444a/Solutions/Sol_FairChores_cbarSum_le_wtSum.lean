-- Prove2me | solution 1 for FairChores.cbarSum_le_wtSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:50.341222+00:00
-- url     : https://prove2.me/submissions/57604485-10a6-41d7-bc90-5cc1897b5dd8

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbar_le_wt

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (A : Finset T) : cbarSum c p A ≤ wtSum c p mu A :=
  Finset.sum_le_sum fun t _ => cbar_le_wt t
end FairChores
