-- Prove2me | solution 1 for FairChores.cbar_le_wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:27.82555+00:00
-- url     : https://prove2.me/submissions/1c9bf9b3-f475-4e83-b6b7-cb76dbaa93c1

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbar_le_price

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (t : T) : cbar c p t ≤ wt c p mu t := by
  unfold wt
  split
  · exact cbar_le_price t
  · exact le_rfl
end FairChores
