-- Prove2me | solution 1 for FairSelling.epsSEF1_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:36:16.441287+00:00
-- url     : https://prove2.me/submissions/e5838f3e-a42f-48b0-81db-db1402d3150e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}


theorem solution : epsSEF1 v p 0 o ↔ SEF1 v p o := by
  simp [epsSEF1,SEF1]
